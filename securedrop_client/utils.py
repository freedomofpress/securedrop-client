import logging
import math
import os
import time

from contextlib import contextmanager
from typing import Dict, Generator, Optional

from sqlalchemy.orm.session import Session

from securedrop_client import db


def safe_mkdir(sdc_home: str, relative_path: str = None) -> None:
    '''
    Safely create directories while checking permissions along the way.
    '''

    if relative_path:
        full_path = os.path.join(sdc_home, relative_path)
    else:
        full_path = sdc_home

    if not full_path == os.path.abspath(full_path):
        raise ValueError('Path is not absolute: {}'.format(full_path))

    if not os.path.exists(sdc_home):
        os.makedirs(sdc_home, 0o700)

    check_dir_permissions(sdc_home)

    if not relative_path:
        return

    path_components = split_path(relative_path)

    path_so_far = sdc_home
    for component in path_components:
        path_so_far = os.path.join(path_so_far, component)
        check_dir_permissions(path_so_far)
        os.makedirs(path_so_far, 0o0700, exist_ok=True)


def check_dir_permissions(dir_path: str) -> None:
    '''
    Check that a directory has ``700`` as the final 3 bytes. Raises a
    ``RuntimeError`` otherwise.
    '''
    if os.path.exists(dir_path):
        stat_res = os.stat(dir_path).st_mode
        masked = stat_res & 0o777
        if masked & 0o077:
            raise RuntimeError('Unsafe permissions ({}) on {}'
                               .format(oct(stat_res), dir_path))


def split_path(path: str) -> list:
    out = []

    while path:
        path, tail = os.path.split(path)
        out.append(tail)

    out.reverse()
    return out


def humanize_filesize(filesize: int) -> str:
    """
    Returns a human readable string of a filesize
    (with an input unit of bytes)
    """
    if filesize < 1024:
        return '{}B'.format(str(filesize))
    elif filesize < 1024 * 1024:
        return '{}KB'.format(math.floor(filesize / 1024))
    else:
        return '{}MB'.format(math.floor(filesize / 1024 ** 2))


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
