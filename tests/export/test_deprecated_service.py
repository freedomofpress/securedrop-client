import os
import subprocess
from tempfile import NamedTemporaryFile, TemporaryDirectory

import pytest
from PyQt5.QtTest import QSignalSpy

from securedrop_client.export import ExportError, ExportStatus
from securedrop_client.export import Service as Export
from securedrop_client.export.archive import Archive
from securedrop_client.export.cli import CLI

# All tests in this file can be removed when the corresponding deprecated API is removed.
# They all have equivalents in th other tests/export/test_*.py files.


def test_print(mocker):
    """
    Ensure TemporaryDirectory is used when creating and sending the archive containing the file to
    print and that the success signal is emitted.
    """
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.service.TemporaryDirectory", return_value=mock_temp_dir)
    export = Export()
    print_call_success_emissions = QSignalSpy(export.print_call_success)
    assert print_call_success_emissions.isValid()
    export_completed_emissions = QSignalSpy(export.export_completed)
    assert export_completed_emissions.isValid()
    print = mocker.patch.object(export._cli, "print")
    mocker.patch("os.path.exists", return_value=True)

    export.print(["path1", "path2"])

    print.assert_called_once_with("mock_temp_dir", ["path1", "path2"])
    assert len(print_call_success_emissions) == 1
    assert print_call_success_emissions[0] == []
    assert len(export_completed_emissions) == 1
    assert export_completed_emissions[0] == [["path1", "path2"]]


def test_print_error(mocker):
    """
    Ensure TemporaryDirectory is used when creating and sending the archive containing the file to
    print and that the failure signal is emitted.
    """
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.service.TemporaryDirectory", return_value=mock_temp_dir)
    export = Export()
    print_call_failure_emissions = QSignalSpy(export.print_call_failure)
    assert print_call_failure_emissions.isValid()
    export_completed_emissions = QSignalSpy(export.export_completed)
    assert export_completed_emissions.isValid()
    error = ExportError("[mock_filepath]")
    print = mocker.patch.object(export._cli, "print", side_effect=error)
    mocker.patch("os.path.exists", return_value=True)

    export.print(["path1", "path2"])

    print.assert_called_once_with("mock_temp_dir", ["path1", "path2"])
    assert len(print_call_failure_emissions) == 1
    assert print_call_failure_emissions[0] == [error]
    assert len(export_completed_emissions) == 1
    assert export_completed_emissions[0] == [["path1", "path2"]]


def test_send_file_to_usb_device(mocker):
    """
    Ensure TemporaryDirectory is used when creating and sending the archive containing the export
    file and that the success signal is emitted.
    """
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.service.TemporaryDirectory", return_value=mock_temp_dir)
    service = Export()
    export_usb_call_success_emissions = QSignalSpy(service.export_usb_call_success)
    assert export_usb_call_success_emissions.isValid()
    export_completed_emissions = QSignalSpy(service.export_completed)
    assert export_completed_emissions.isValid()
    export = mocker.patch.object(service._cli, "export")
    mocker.patch("os.path.exists", return_value=True)

    service.export(["path1", "path2"], "mock passphrase")

    export.assert_called_once_with("mock_temp_dir", ["path1", "path2"], "mock passphrase")
    assert len(export_usb_call_success_emissions) == 1
    assert export_usb_call_success_emissions[0] == []
    assert len(export_completed_emissions) == 1
    assert export_completed_emissions[0] == [["path1", "path2"]]


def test_send_file_to_usb_device_error(mocker):
    """
    Ensure TemporaryDirectory is used when creating and sending the archive containing the export
    file and that the failure signal is emitted.
    """
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.service.TemporaryDirectory", return_value=mock_temp_dir)
    service = Export()
    export_usb_call_failure_emissions = QSignalSpy(service.export_usb_call_failure)
    assert export_usb_call_failure_emissions.isValid()
    export_completed_emissions = QSignalSpy(service.export_completed)
    assert export_completed_emissions.isValid()
    error = ExportError("[mock_filepath]")
    export = mocker.patch.object(service._cli, "export", side_effect=error)
    mocker.patch("os.path.exists", return_value=True)

    service.export(["path1", "path2"], "mock passphrase")

    export.assert_called_once_with("mock_temp_dir", ["path1", "path2"], "mock passphrase")
    assert len(export_usb_call_failure_emissions) == 1
    assert export_usb_call_failure_emissions[0] == [error]
    assert len(export_completed_emissions) == 1
    assert export_completed_emissions[0] == [["path1", "path2"]]


def test_check_disk(mocker):
    """
    Ensure TemporaryDirectory is used when creating and sending the archives during the preflight
    checks and that the success signal is emitted by Export.
    """
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.service.TemporaryDirectory", return_value=mock_temp_dir)
    service = Export()
    preflight_check_call_success_emissions = QSignalSpy(service.preflight_check_call_success)
    assert preflight_check_call_success_emissions.isValid()
    check_disk_presence = mocker.patch.object(service._cli, "check_disk_presence")
    check_disk_encryption = mocker.patch.object(service._cli, "check_disk_encryption")

    service.check_disk()

    check_disk_presence.assert_called_once_with("mock_temp_dir")
    check_disk_encryption.assert_called_once_with("mock_temp_dir")
    assert len(preflight_check_call_success_emissions) == 1
    assert preflight_check_call_success_emissions[0] == []


def test_check_disk_error(mocker):
    """
    Ensure TemporaryDirectory is used when creating and sending the archives during the preflight
    checks and that the failure signal is emitted by Export.
    """
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.service.TemporaryDirectory", return_value=mock_temp_dir)
    service = Export()
    preflight_check_call_failure_emissions = QSignalSpy(service.preflight_check_call_failure)
    assert preflight_check_call_failure_emissions.isValid()
    error = ExportError("bang!")
    check_disk_presence = mocker.patch.object(service._cli, "check_disk_presence")
    check_disk_encryption = mocker.patch.object(
        service._cli, "check_disk_encryption", side_effect=error
    )

    service.check_disk()

    check_disk_presence.assert_called_once_with("mock_temp_dir")
    check_disk_encryption.assert_called_once_with("mock_temp_dir")
    assert len(preflight_check_call_failure_emissions) == 1
    assert preflight_check_call_failure_emissions[0] == [error]


def test__create_archive(mocker):
    """
    Ensure create_archive creates an archive in the supplied directory.
    """
    archive_path = None
    with TemporaryDirectory() as temp_dir:
        archive_path = Archive.create_archive(temp_dir, "mock.sd-export", {})
        assert archive_path == os.path.join(temp_dir, "mock.sd-export")
        assert os.path.exists(archive_path)  # sanity check

    assert not os.path.exists(archive_path)


def test__create_archive_with_an_export_file(mocker):
    archive_path = None
    with TemporaryDirectory() as temp_dir, NamedTemporaryFile() as export_file:
        archive_path = Archive.create_archive(temp_dir, "mock.sd-export", {}, [export_file.name])
        assert archive_path == os.path.join(temp_dir, "mock.sd-export")
        assert os.path.exists(archive_path)  # sanity check

    assert not os.path.exists(archive_path)


def test__create_archive_with_multiple_export_files(mocker):
    """
    Ensure an archive
    """
    archive_path = None
    with TemporaryDirectory() as temp_dir, NamedTemporaryFile() as export_file_one, NamedTemporaryFile() as export_file_two:  # noqa
        archive_path = Archive.create_archive(
            temp_dir, "mock.sd-export", {}, [export_file_one.name, export_file_two.name]
        )
        assert archive_path == os.path.join(temp_dir, "mock.sd-export")
        assert os.path.exists(archive_path)  # sanity check

    assert not os.path.exists(archive_path)


def test__export_archive(mocker):
    """
    Ensure the subprocess call returns the expected output.
    """
    mocker.patch("subprocess.check_output", return_value=b"USB_CONNECTED")
    status = CLI._export_archive("mock.sd-export")
    assert status == ExportStatus.USB_CONNECTED

    mocker.patch("subprocess.check_output", return_value=b"mock")
    with pytest.raises(ExportError, match="UNEXPECTED_RETURN_STATUS"):
        CLI._export_archive("mock.sd-export")


def test__export_archive_does_not_raise_ExportError_when_CalledProcessError(mocker):
    """
    Ensure ExportError is raised if a CalledProcessError is encountered.
    """
    mock_error = subprocess.CalledProcessError(cmd=["mock_cmd"], returncode=123)
    mocker.patch("subprocess.check_output", side_effect=mock_error)

    with pytest.raises(ExportError, match="CALLED_PROCESS_ERROR"):
        CLI._export_archive("mock.sd-export")


def test__export_archive_with_evil_command(mocker):
    """
    Ensure shell command is shell-escaped.
    """
    check_output = mocker.patch("subprocess.check_output", return_value=b"ERROR_FILE_NOT_FOUND")

    with pytest.raises(ExportError, match="UNEXPECTED_RETURN_STATUS"):
        CLI._export_archive("somefile; rm -rf ~")

    check_output.assert_called_once_with(
        [
            "qrexec-client-vm",
            "--",
            "sd-devices",
            "qubes.OpenInVM",
            "/usr/lib/qubes/qopen-in-vm",
            "--view-only",
            "--",
            "'somefile; rm -rf ~'",
        ],
        stderr=-2,
    )


def test__export_archive_success_on_empty_return_value(mocker):
    """
    Ensure an error is not raised when qrexec call returns empty string,
    (success state for `disk`, `print`, `printer-test`).

    When export behaviour changes so that all success states return a status
    string, this test will no longer pass and should be rewritten.
    """
    check_output = mocker.patch(
        "securedrop_client.export.cli.subprocess.check_output", return_value=b""
    )

    result = CLI._export_archive("somefile.sd-export")

    check_output.assert_called_once_with(
        [
            "qrexec-client-vm",
            "--",
            "sd-devices",
            "qubes.OpenInVM",
            "/usr/lib/qubes/qopen-in-vm",
            "--view-only",
            "--",
            "somefile.sd-export",
        ],
        stderr=-2,
    )

    assert result is None
