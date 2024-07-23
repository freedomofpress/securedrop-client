import json
import os
import subprocess  # noqa: F401
import tarfile
import tempfile
from io import BytesIO
from unittest import mock

import pytest

from securedrop_export.archive import Archive, Metadata, Status
from securedrop_export.exceptions import ExportException


def test_extract_tarball():
    """
    Check that we can successfully extract a valid tarball.
    """
    with tempfile.TemporaryDirectory() as temp_dir:
        archive_path = os.path.join(temp_dir, "archive.sd-export")
        with tarfile.open(archive_path, "w:gz") as archive:
            metadata = {
                "device": "disk",
                "encryption_key": "test",
            }
            metadata_str = json.dumps(metadata)
            metadata_bytes = BytesIO(metadata_str.encode("utf-8"))
            metadata_file_info = tarfile.TarInfo("metadata.json")
            metadata_file_info.size = len(metadata_str)
            archive.addfile(metadata_file_info, metadata_bytes)
            content = b"test"
            file_info = tarfile.TarInfo("some/dirs/file.txt")
            file_info.size = len(content)
            file_info.mode = 0o777
            archive.addfile(file_info, BytesIO(content))

            dir_info = tarfile.TarInfo("some")
            dir_info.type = tarfile.DIRTYPE
            dir_info.mode = 0o777
            archive.addfile(dir_info)

            archive.close()

        submission = Archive(archive_path).extract_tarball()
        assert oct(os.stat(submission.tmpdir).st_mode) == "0o40700"

        extracted_file_path = os.path.join(submission.tmpdir, "some", "dirs", "file.txt")
        assert os.path.exists(extracted_file_path)
        assert oct(os.stat(extracted_file_path).st_mode) == "0o100600"

        # Subdirectories that are added as members are extracted with 700 permissions
        assert oct(os.stat(os.path.join(submission.tmpdir, "some")).st_mode) == "0o40700"
        # Subdirectories that are not added as members are extracted with 700 permissions
        # because os.umask(0o077) is set in the Archive constructor.
        assert oct(os.stat(os.path.join(submission.tmpdir, "some", "dirs")).st_mode) == "0o40700"


def test_extract_tarball_with_symlink():
    """
    Check that we can successfully extract a valid tarball that contains a valid symlink.
    """
    with tempfile.TemporaryDirectory() as temp_dir:
        archive_path = os.path.join(temp_dir, "archive.sd-export")
        with tarfile.open(archive_path, "w:gz") as archive:
            metadata = {
                "device": "disk",
                "encryption_key": "test",
            }
            metadata_str = json.dumps(metadata)
            metadata_bytes = BytesIO(metadata_str.encode("utf-8"))
            metadata_file_info = tarfile.TarInfo("metadata.json")
            metadata_file_info.size = len(metadata_str)
            archive.addfile(metadata_file_info, metadata_bytes)
            symlink_info = tarfile.TarInfo("symlink")
            symlink_info.type = tarfile.SYMTYPE
            symlink_info.linkname = "file"
            archive.addfile(symlink_info)
            archive.close()

        submission = Archive(archive_path)
        assert oct(os.stat(submission.tmpdir).st_mode) == "0o40700"

        submission = submission.extract_tarball()

        symlink_path = os.path.join(submission.tmpdir, "symlink")
        assert os.path.islink(symlink_path)


def test_extract_tarball_raises_if_doing_path_traversal():
    """
    Check that we do not allow tarfile member file to do path traversal via TarInfo.name.
    """
    if os.path.exists("/tmp/traversed"):
        os.remove("/tmp/traversed")

    with tempfile.TemporaryDirectory() as temp_dir:
        archive_path = os.path.join(temp_dir, "archive.sd-export")
        with tarfile.open(archive_path, "w:gz") as archive:
            metadata = {
                "device": "disk",
                "encryption_key": "test",
            }
            metadata_str = json.dumps(metadata)
            metadata_bytes = BytesIO(metadata_str.encode("utf-8"))
            metadata_file_info = tarfile.TarInfo("metadata.json")
            metadata_file_info.size = len(metadata_str)
            archive.addfile(metadata_file_info, metadata_bytes)
            content = b"test"
            traversed_file_info = tarfile.TarInfo("../../../../../../../../../tmp/traversed")
            traversed_file_info.size = len(content)
            archive.addfile(traversed_file_info, BytesIO(content))
            archive.close()

        submission = Archive(archive_path)

        with pytest.raises(ExportException):
            submission.extract_tarball()

        assert not os.path.exists("/tmp/traversed")


def test_extract_tarball_raises_if_doing_path_traversal_with_dir():
    """
    Check that we do not allow tarfile member directory to do path traversal via TarInfo.name.
    """
    if os.path.exists("/tmp/traversed/"):
        os.rmdir("/tmp/traversed/")

    if os.path.exists("/tmp/traversed"):
        os.remove("/tmp/traversed")

    with tempfile.TemporaryDirectory() as temp_dir:
        archive_path = os.path.join(temp_dir, "archive.sd-export")
        with tarfile.open(archive_path, "w:gz") as archive:
            metadata = {
                "device": "disk",
                "encryption_key": "test",
            }
            metadata_str = json.dumps(metadata)
            metadata_bytes = BytesIO(metadata_str.encode("utf-8"))
            metadata_file_info = tarfile.TarInfo("metadata.json")
            metadata_file_info.size = len(metadata_str)
            archive.addfile(metadata_file_info, metadata_bytes)
            dir_info = tarfile.TarInfo("../../../../../../../../../tmp/traversed")
            dir_info.type = tarfile.DIRTYPE
            dir_info.mode = 0o777
            archive.addfile(dir_info)
            archive.close()

        submission = Archive(archive_path)

        with pytest.raises(ExportException):
            submission.extract_tarball()

        assert not os.path.exists("/tmp/traversed")


def test_extract_tarball_raises_if_doing_path_traversal_with_symlink():
    """
    Check that we do not allow tarfile member symlink to do path traversal via TarInfo.name.
    """
    if os.path.exists("/tmp/traversed/"):
        os.rmdir("/tmp/traversed/")

    if os.path.exists("/tmp/traversed"):
        os.remove("/tmp/traversed")

    with tempfile.TemporaryDirectory() as temp_dir:
        archive_path = os.path.join(temp_dir, "archive.sd-export")
        with tarfile.open(archive_path, "w:gz") as archive:
            metadata = {
                "device": "disk",
                "encryption_key": "test",
            }
            metadata_str = json.dumps(metadata)
            metadata_bytes = BytesIO(metadata_str.encode("utf-8"))
            metadata_file_info = tarfile.TarInfo("metadata.json")
            metadata_file_info.size = len(metadata_str)
            archive.addfile(metadata_file_info, metadata_bytes)
            content = b"test"
            symlink_info = tarfile.TarInfo("symlink")
            symlink_info.size = len(content)
            symlink_info.type = tarfile.SYMTYPE
            symlink_info.name = "../../../../../../../../../tmp/traversed"
            archive.addfile(symlink_info, BytesIO(content))
            archive.close()

        submission = Archive(archive_path)

        with pytest.raises(ExportException):
            submission.extract_tarball()

        assert not os.path.exists("/tmp/traversed")


def test_extract_tarball_raises_if_doing_path_traversal_with_symlink_linkname():
    """
    Check that we do not allow tarfile member symlink to do path traversal via TarInfo.linkname.
    """
    if os.path.exists("/tmp/traversed/"):
        os.rmdir("/tmp/traversed/")

    if os.path.exists("/tmp/traversed"):
        os.remove("/tmp/traversed")

    with tempfile.TemporaryDirectory() as temp_dir:
        archive_path = os.path.join(temp_dir, "archive.sd-export")
        with tarfile.open(archive_path, "w:gz") as archive:
            metadata = {
                "device": "disk",
                "encryption_key": "test",
            }
            metadata_str = json.dumps(metadata)
            metadata_bytes = BytesIO(metadata_str.encode("utf-8"))
            metadata_file_info = tarfile.TarInfo("metadata.json")
            metadata_file_info.size = len(metadata_str)
            archive.addfile(metadata_file_info, metadata_bytes)
            content = b"test"
            symlink_info = tarfile.TarInfo("symlink")
            symlink_info.size = len(content)
            symlink_info.type = tarfile.SYMTYPE
            symlink_info.linkname = "../../../../../../../../../tmp/traversed"
            archive.addfile(symlink_info, BytesIO(content))
            archive.close()

        submission = Archive(archive_path)

        with pytest.raises(ExportException):
            submission.extract_tarball()

        assert not os.path.exists("/tmp/traversed")


def test_extract_tarball_raises_if_name_has_unsafe_absolute_path():
    """
    Check that we do not allow tarfile member file to specify an unsafe absolute path via
    TarInfo.name.
    """
    if os.path.exists("/tmp/unsafe"):
        os.remove("/tmp/unsafe")

    with tempfile.TemporaryDirectory() as temp_dir:
        archive_path = os.path.join(temp_dir, "archive.sd-export")
        with tarfile.open(archive_path, "w:gz") as archive:
            metadata = {
                "device": "disk",
                "encryption_key": "test",
            }
            metadata_str = json.dumps(metadata)
            metadata_bytes = BytesIO(metadata_str.encode("utf-8"))
            metadata_file_info = tarfile.TarInfo("metadata.json")
            metadata_file_info.size = len(metadata_str)
            archive.addfile(metadata_file_info, metadata_bytes)
            content = b"test"
            file_info = tarfile.TarInfo("/tmp/unsafe")
            file_info.size = len(content)
            file_info.mode = 0o777
            archive.addfile(file_info, BytesIO(content))
            archive.close()

        submission = Archive(archive_path)

        with pytest.raises(ExportException):
            submission.extract_tarball()

        assert not os.path.exists("/tmp/unsafe")


def test_extract_tarball_raises_if_name_has_unsafe_absolute_path_with_symlink():
    """
    Check that we do not allow tarfile member symlink to specify an unsafe absolute path via
    TarInfo.name.
    """
    if os.path.exists("/tmp/unsafe"):
        os.remove("/tmp/unsafe")

    tmp = tempfile.gettempdir()
    with tempfile.TemporaryDirectory() as temp_dir:
        archive_path = os.path.join(temp_dir, "archive.sd-export")
        symlink_path = os.path.join(temp_dir, "symlink")

        os.system(f"ln -s {tmp}/unsafe {symlink_path}")  # create symlink to "/tmp/unsafe"

        with tarfile.open(archive_path, "w:gz") as archive:
            metadata = {
                "device": "disk",
                "encryption_key": "test",
            }
            metadata_str = json.dumps(metadata)
            metadata_bytes = BytesIO(metadata_str.encode("utf-8"))
            metadata_file_info = tarfile.TarInfo("metadata.json")
            metadata_file_info.size = len(metadata_str)
            archive.addfile(metadata_file_info, metadata_bytes)
            archive.add(symlink_path, "symlink")
            archive.close()

        submission = Archive(archive_path)

        with pytest.raises(ExportException):
            submission.extract_tarball()

        assert not os.path.exists("/tmp/unsafe")


def test_extract_tarball_raises_if_name_has_unsafe_absolute_path_with_symlink_to_dir():
    """
    Check that we do not allow tarfile member symlink to specify an unsafe absolute path via
    TarInfo.name.

    Note: Same test as `test_extract_tarball_raises_if_name_has_unsafe_absolute_path_with_symlink`
    but checks that symlinks to absolute directories are also caught.
    """
    if os.path.exists("/tmp/unsafe"):
        os.remove("/tmp/unsafe")

    tmp = tempfile.gettempdir()
    with tempfile.TemporaryDirectory() as temp_dir:
        archive_path = os.path.join(temp_dir, "archive.sd-export")
        symlink_path = os.path.join(temp_dir, "symlink")
        file_path = os.path.join(temp_dir, "unsafe")

        with open(file_path, "w") as file:
            file.write("some-content")

        os.system(f"ln -s {tmp} {symlink_path}")  # create symlink to "/tmp"

        with tarfile.open(archive_path, "w:gz") as archive:
            metadata = {
                "device": "disk",
                "encryption_key": "test",
            }
            metadata_str = json.dumps(metadata)
            metadata_bytes = BytesIO(metadata_str.encode("utf-8"))
            metadata_file_info = tarfile.TarInfo("metadata.json")
            metadata_file_info.size = len(metadata_str)
            archive.addfile(metadata_file_info, metadata_bytes)
            archive.add(symlink_path, "symlink")
            archive.add(file_path, "symlink/unsafe")
            archive.close()

        submission = Archive(archive_path)

        with pytest.raises(ExportException):
            submission.extract_tarball()

        assert not os.path.exists("/tmp/unsafe")


def test_extract_tarball_raises_if_linkname_has_unsafe_absolute_path():
    """
    Check that we do not allow tarfile member file to specify an unsafe absolute path via
    TarInfo.linkname.
    """
    if os.path.exists("/tmp/unsafe"):
        os.remove("/tmp/unsafe")

    with tempfile.TemporaryDirectory() as temp_dir:
        archive_path = os.path.join(temp_dir, "archive.sd-export")
        with tarfile.open(archive_path, "w:gz") as archive:
            metadata = {
                "device": "disk",
                "encryption_key": "test",
            }
            metadata_str = json.dumps(metadata)
            metadata_bytes = BytesIO(metadata_str.encode("utf-8"))
            metadata_file_info = tarfile.TarInfo("metadata.json")
            metadata_file_info.size = len(metadata_str)
            archive.addfile(metadata_file_info, metadata_bytes)
            content = b"test"
            symlink_info = tarfile.TarInfo("symlink")
            symlink_info.size = len(content)
            symlink_info.type = tarfile.SYMTYPE
            symlink_info.linkname = "/tmp/unsafe"
            archive.addfile(symlink_info, BytesIO(content))
            archive.close()

        submission = Archive(archive_path)

        with pytest.raises(ExportException):
            submission.extract_tarball()

        assert not os.path.exists("/tmp/unsafe")


def test_empty_config(capsys):
    Archive("testfile")
    temp_folder = tempfile.mkdtemp()
    metadata = os.path.join(temp_folder, Metadata.METADATA_FILE)
    with open(metadata, "w") as f:
        f.write("{}")

    with pytest.raises(ExportException) as ex:
        Metadata(temp_folder).validate()
    assert ex.value.sdstatus is Status.ERROR_ARCHIVE_METADATA


def test_valid_printer_test_config(capsys):
    Archive("testfile")
    temp_folder = tempfile.mkdtemp()
    metadata = os.path.join(temp_folder, Metadata.METADATA_FILE)
    with open(metadata, "w") as f:
        f.write('{"device": "printer-test"}')

    config = Metadata(temp_folder).validate()

    assert config.encryption_key is None


def test_valid_printer_config(capsys):
    Archive("")
    temp_folder = tempfile.mkdtemp()
    metadata = os.path.join(temp_folder, Metadata.METADATA_FILE)
    with open(metadata, "w") as f:
        f.write('{"device": "printer"}')

    config = Metadata(temp_folder).validate()

    assert config.encryption_key is None


def test_invalid_config(capsys):
    Archive("testfile")

    temp_folder = tempfile.mkdtemp()
    metadata = os.path.join(temp_folder, Metadata.METADATA_FILE)
    with open(metadata, "w") as f:
        f.write('{"device": "asdf"}')

    with pytest.raises(ExportException) as ex:
        Metadata(temp_folder).validate()

    assert ex.value.sdstatus is Status.ERROR_ARCHIVE_METADATA


def test_malformed_config(capsys):
    Archive("testfile")

    temp_folder = tempfile.mkdtemp()
    metadata = os.path.join(temp_folder, Metadata.METADATA_FILE)
    with open(metadata, "w") as f:
        f.write('{"device": {"OHNO", "MALFORMED"}')

    with pytest.raises(ExportException) as ex:
        Metadata(temp_folder).validate()

    assert ex.value.sdstatus is Status.ERROR_METADATA_PARSING


def test_valid_encryption_config(capsys):
    Archive("testfile")
    temp_folder = tempfile.mkdtemp()
    metadata = os.path.join(temp_folder, Metadata.METADATA_FILE)
    with open(metadata, "w") as f:
        f.write('{"device": "disk", "encryption_key": "hunter1"}')

    config = Metadata(temp_folder).validate()

    assert config.encryption_key == "hunter1"


@mock.patch("json.loads", side_effect=json.decoder.JSONDecodeError("ugh", "badjson", 0))
def test_metadata_parsing_error(mock_json):
    """
    Handle exception caused when loading metadata JSON
    """
    with pytest.raises(ExportException) as ex:
        Metadata(tempfile.mkdtemp()).validate()

    assert ex.value.sdstatus is Status.ERROR_METADATA_PARSING
