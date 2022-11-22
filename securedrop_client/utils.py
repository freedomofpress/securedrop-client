import gzip
import logging
import math
import os
import shutil
import time
from contextlib import contextmanager
from pathlib import Path
from typing import BinaryIO, Dict, Generator, Optional, Union

from sqlalchemy.orm.session import Session

from securedrop_client import db


def safe_mkdir(
    base_path: Union[Path, str], relative_path: Union[Optional[Path], Optional[str]] = None
) -> None:
    """
    Safely create directories with restricted 700 permissions inside the base_path directory. The
    caller of this function should ensure that base_path comes from a hard-coded string.

    Raises FileNotFoundError if base_path does not already exist or requires more than one new dir
    Raises RuntimeError if any dir in relative_path or the last dir of base_path have insecure perms
    Raises ValueError if any of the following conditions is true:
      * base_dir fails path traversal check, e.g. "/home/../traversed" fails check
      * the resolved relative_path is not a subdirectory of base_path
      * a child directory in relative_path already exists with permissions other than 700
    """
    base_path = Path(base_path)
    if not base_path.is_absolute():
        raise ValueError(f"Base directory '{base_path}' must be an absolute path")

    check_path_traversal(base_path)

    if relative_path:
        check_path_traversal(relative_path)
        full_path = base_path.joinpath(relative_path)
    else:
        full_path = base_path

    # Create each parent directory, including base_path, first.
    #
    # Note: We do not use parents=True because the parent directories will not be created with the
    # specified mode. Parents are created using system default permissions, which we modify to be
    # 700 via os.umask in the Window (QMainWindow) constructor. Creating directories one-by-one with
    # mode=0o0700 is not necessary but adds defense in depth.
    relative_path = relative_filepath(full_path, base_path)
    for parent in reversed(relative_path.parents):
        base_path.joinpath(parent).mkdir(mode=0o0700, exist_ok=True)

    # Now create the full_path directory.
    full_path.mkdir(mode=0o0700, exist_ok=True)

    # Check permissions after creating the directories
    check_all_permissions(relative_path, base_path)


def safe_gzip_extract(
    gzip_file_path: str, dest_path: str, original_filename: str, base_path: str
) -> None:
    """
    Safely unzip a file specified by gzip_file_path to dest_path, replacing filename with
    original_filename.
    """
    dest_dir = Path(dest_path).parent
    safe_mkdir(base_path, str(dest_dir))

    dest_path_with_original_filename = dest_dir.joinpath(original_filename)
    with gzip.open(gzip_file_path, "rb") as src_file, open(
        dest_path_with_original_filename, "wb"
    ) as dest_file:
        safe_copyfileobj(src_file, dest_file, base_path)


def safe_move(src_path: str, dest_path: str, dest_base_path: str) -> None:
    """
    Safely move src_path to dest_path.
    """
    check_path_traversal(src_path)
    check_path_traversal(dest_path)
    # Ensure directories in dest_path are created safely if they don't exist
    safe_mkdir(dest_base_path, Path(dest_path).parent)
    shutil.move(src_path, dest_path)
    Path(dest_path).chmod(0o600)


def safe_copy(src_path: str, dest_path: str, dest_base_path: str) -> None:
    """
    Safely copy a file specified by src_path to dest_path.

    TODO: Figure out a clearer way to safely copy to a temporary file that gets
    deleted right away. We may need a safe_decrypt function in the future.
    """
    check_path_traversal(src_path)
    check_path_traversal(dest_path)
    relative_filepath(dest_path, dest_base_path)
    shutil.copy(src_path, dest_path)
    Path(dest_path).chmod(0o600)


def safe_copyfileobj(src_file: gzip.GzipFile, dest_file: BinaryIO, dest_base_path: str) -> None:
    """
    Safely copy src_file to dest_file.
    """
    check_path_traversal(src_file.name)
    check_path_traversal(dest_file.name)
    # Ensure directories of dest_file are created safely if they don't exist
    safe_mkdir(dest_base_path, Path(dest_file.name).parent)
    shutil.copyfileobj(src_file, dest_file)
    Path(dest_file.name).chmod(0o600)


def relative_filepath(filepath: Union[str, Path], base_dir: Union[str, Path]) -> Path:
    """
    Raise ValueError if the filepath is not relative to the supplied base_dir or if base_dir is not
    an absolute path.

    Note: resolve() will also resolve symlinks, so a symlink such as /tmp/tmp1a2s3d4f/innocent
    that points to ../../../../../tmp/traversed will raise a ValueError if the base_dir is the
    expected /tmp/tmp1a2s3d4f.
    """
    return Path(filepath).resolve().relative_to(base_dir)


def check_path_traversal(filename_or_filepath: Union[str, Path]) -> None:
    """
    Raise ValueError if filename_or_filepath does any path traversal. This works on filenames,
    relative paths, and absolute paths.
    """
    filename_or_filepath = Path(filename_or_filepath)

    if filename_or_filepath.is_absolute():
        base_path = filename_or_filepath
    else:
        base_path = Path.cwd()  # use cwd so we can next ensure relative path does not traverse up

    try:
        relative_path = relative_filepath(filename_or_filepath, base_path)

        # One last check just to cover "weird/../traversals" that may not traverse past the
        # base directory, but can still have harmful side effects to the application. If this
        # kind of traversal is needed, then call relative_filepath instead in order to check
        # that the desired traversal does not go past a safe base directory.
        if relative_path != filename_or_filepath and not filename_or_filepath.is_absolute():
            raise ValueError
    except ValueError:
        raise ValueError(f"Unsafe file or directory name: '{filename_or_filepath}'")


def check_all_permissions(path: Union[str, Path], base_path: Union[str, Path]) -> None:
    """
    Check that the permissions of each directory between base_path and path are set to 700.
    """
    base_path = Path(base_path)
    full_path = base_path.joinpath(path)
    if not full_path.exists():
        return

    Path(full_path).chmod(0o700)
    check_dir_permissions(full_path)

    relative_path = relative_filepath(full_path, base_path)
    for parent in relative_path.parents:
        full_path = base_path.joinpath(parent)
        Path(full_path).chmod(0o700)
        check_dir_permissions(str(full_path))


def check_dir_permissions(dir_path: Union[str, Path]) -> None:
    """
    Check that a directory has ``700`` as the final 3 bytes. Raises a ``RuntimeError`` otherwise.
    """
    if os.path.exists(dir_path):
        stat_res = os.stat(dir_path).st_mode
        masked = stat_res & 0o777
        if masked & 0o077:
            raise RuntimeError("Unsafe permissions ({}) on {}".format(oct(stat_res), dir_path))


def humanize_filesize(filesize: int) -> str:
    """
    Returns a human readable string of a filesize
    (with an input unit of bytes)
    """
    if filesize < 1024:
        return "{}B".format(str(filesize))
    elif filesize < 1024 * 1024:
        return "{}KB".format(math.floor(filesize / 1024))
    else:
        return "{}MB".format(math.floor(filesize / 1024**2))


@contextmanager
def chronometer(logger: logging.Logger, description: str) -> Generator:
    """
    Measures the execution time of its block.
    """
    try:
        start = time.perf_counter()
        yield
    finally:
        elapsed = time.perf_counter() - start
        logger.info(f"{description} duration: {elapsed:.4f}s")


class SourceCache(object):
    """
    Caches Sources by UUID.
    """

    def __init__(self, session: Session) -> None:
        super().__init__()
        self.cache: Dict[str, db.Source] = {}
        self.session = session

    def get(self, source_uuid: str) -> Optional[db.Source]:
        if source_uuid not in self.cache:
            source = self.session.query(db.Source).filter_by(uuid=source_uuid).first()
            self.cache[source_uuid] = source
        return self.cache.get(source_uuid)
