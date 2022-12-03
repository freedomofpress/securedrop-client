import os
import subprocess
import unittest
from tempfile import NamedTemporaryFile, TemporaryDirectory
from unittest.mock import MagicMock, patch

import pytest
from PyQt5.QtTest import QSignalSpy

from securedrop_client import export
from securedrop_client.export import ExportError, ExportStatus
from securedrop_client.export import Service as Export


class TestExportService(unittest.TestCase):
    def test_export_service_is_unique(self):
        export_service = export.getService()
        same_export_service = export.getService()

        self.assertTrue(
            export_service is same_export_service,
            "expected successive calls to export.getService to return the same service instance",  # noqa: E501
        )

    @patch(
        "securedrop_client.export.service.TemporaryDirectory.__enter__",
        return_value="tmpdir-sq324f",
    )
    @patch.object(export.Service, "_check_printer_status")
    def test_uses_temporary_directory_for_printer_status_check(
        self, _check_printer_status, _tmpdir
    ):
        export_service = export.getService()

        export_service.check_printer_status()

        _check_printer_status.assert_called_once_with("tmpdir-sq324f")

    @patch("securedrop_client.export.service.TemporaryDirectory")
    @patch.object(export.Service, "_check_printer_status")
    def test_emits_printer_found_ready_when_printer_status_check_succeeds(
        self, _check_printer_status, _temporary_directory
    ):
        export_service = export.getService()
        printer_found_ready_emissions = QSignalSpy(export_service.printer_found_ready)
        assert printer_found_ready_emissions.isValid()

        export_service.check_printer_status()

        assert len(printer_found_ready_emissions) == 1
        assert printer_found_ready_emissions[0] == []

    @patch("securedrop_client.export.service.TemporaryDirectory")
    @patch.object(export.Service, "_check_printer_status")
    def test_emits_printer_not_found_ready_when_printer_status_check_fails(
        self, _check_printer_status, _temporary_directory
    ):
        expected_error = ExportError("bang!")
        _check_printer_status.side_effect = expected_error
        export_service = export.getService()
        printer_not_found_ready_emissions = QSignalSpy(export_service.printer_not_found_ready)
        assert printer_not_found_ready_emissions.isValid()

        export_service.check_printer_status()

        assert len(printer_not_found_ready_emissions) == 1
        assert printer_not_found_ready_emissions[0] == [expected_error]


class TestExportServiceInterfaceWithCLI(unittest.TestCase):
    def test_internal_printer_status_check_returns_without_errors_when_empty_response(self):
        SUCCESS_STATUS = ""  # sd-devices API
        export_service = export.getService()
        valid_archive_path = "archive_path_13kn3"
        export_service._create_archive = MagicMock()
        export_service._export_archive = MagicMock(return_value=SUCCESS_STATUS)

        export_service._check_printer_status(valid_archive_path)  # testing internal details

        assert True  # no exception was raised

    def test_internal_printer_status_check_exports_a_specifically_created_archive(self):
        expected_archive_path = "archive_path_9f483f"
        expected_archive_dir = "archive_dir_2i19c"
        export_service = export.getService()
        export_service._create_archive = MagicMock(return_value=expected_archive_path)
        export_service._export_archive = MagicMock(return_value="")  # "magic" value

        export_service._check_printer_status(expected_archive_dir)  # testing internal details

        export_service._export_archive.assert_called_once_with(expected_archive_path)
        export_service._create_archive.assert_called_once_with(
            expected_archive_dir, "printer-preflight.sd-export", {"device": "printer-preflight"}
        )

    def test_internal_printer_status_check_raises_export_error_when_not_USB_CONNECTED(self):
        not_USB_CONNECTED = "whatever"
        valid_archive_path = "archive_path_034d3"
        export_service = export.getService()
        export_service._create_archive = MagicMock()
        export_service._export_archive = MagicMock(return_value=not_USB_CONNECTED)

        with pytest.raises(ExportError):
            export_service._check_printer_status(valid_archive_path)  # testing internal details


# All tests below this line can be removed when the corresponding deprecated API is removed.
# They all have equivalents above this line.


def test_run_printer_preflight(mocker):  # DEPRECATED
    """
    Ensure TemporaryDirectory is used when creating and sending the archives during the preflight
    checks and that the success signal is emitted by Export.
    """
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.service.TemporaryDirectory", return_value=mock_temp_dir)
    export = Export()
    printer_preflight_success_emissions = QSignalSpy(export.printer_preflight_success)
    assert printer_preflight_success_emissions.isValid()
    _run_printer_preflight = mocker.patch.object(export, "_run_printer_preflight")

    export.run_printer_preflight()

    _run_printer_preflight.assert_called_once_with("mock_temp_dir")
    assert len(printer_preflight_success_emissions) == 1
    assert printer_preflight_success_emissions[0] == []


def test_run_printer_preflight_error(mocker):  # DEPRECATED
    """
    Ensure TemporaryDirectory is used when creating and sending the archives during the preflight
    checks and that the failure signal is emitted by Export.
    """
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.service.TemporaryDirectory", return_value=mock_temp_dir)
    export = Export()
    printer_preflight_failure_emissions = QSignalSpy(export.printer_preflight_failure)
    assert printer_preflight_failure_emissions.isValid()
    error = ExportError("bang!")
    _run_print_preflight = mocker.patch.object(export, "_run_printer_preflight", side_effect=error)

    export.run_printer_preflight()

    _run_print_preflight.assert_called_once_with("mock_temp_dir")
    assert len(printer_preflight_failure_emissions) == 1
    assert printer_preflight_failure_emissions[0] == [error]


def test__run_printer_preflight(mocker):  # DEPRECATED
    """
    Ensure _export_archive and _create_archive are called with the expected parameters,
    _export_archive is called with the return value of _create_archive, and
    _run_disk_test returns without error if 'USB_CONNECTED' is the return value of _export_archive.
    """
    export = Export()
    export._create_archive = mocker.MagicMock(return_value="mock_archive_path")
    export._export_archive = mocker.MagicMock(return_value="")

    export._run_printer_preflight("mock_archive_dir")

    export._export_archive.assert_called_once_with("mock_archive_path")
    export._create_archive.assert_called_once_with(
        "mock_archive_dir", "printer-preflight.sd-export", {"device": "printer-preflight"}
    )


def test__run_printer_preflight_raises_ExportError_if_not_empty_string(mocker):  # DEPRECATED
    """
    Ensure ExportError is raised if _run_disk_test returns anything other than 'USB_CONNECTED'.
    """
    export = Export()
    export._create_archive = mocker.MagicMock(return_value="mock_archive_path")
    export._export_archive = mocker.MagicMock(return_value="SOMETHING_OTHER_THAN_EMPTY_STRING")

    with pytest.raises(ExportError):
        export._run_printer_preflight("mock_archive_dir")


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
    _run_print = mocker.patch.object(export, "_run_print")
    mocker.patch("os.path.exists", return_value=True)

    export.print(["path1", "path2"])

    _run_print.assert_called_once_with("mock_temp_dir", ["path1", "path2"])
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
    _run_print = mocker.patch.object(export, "_run_print", side_effect=error)
    mocker.patch("os.path.exists", return_value=True)

    export.print(["path1", "path2"])

    _run_print.assert_called_once_with("mock_temp_dir", ["path1", "path2"])
    assert len(print_call_failure_emissions) == 1
    assert print_call_failure_emissions[0] == [error]
    assert len(export_completed_emissions) == 1
    assert export_completed_emissions[0] == [["path1", "path2"]]


def test__run_print(mocker):
    """
    Ensure _export_archive and _create_archive are called with the expected parameters and
    _export_archive is called with the return value of _create_archive.
    """
    export = Export()
    export._create_archive = mocker.MagicMock(return_value="mock_archive_path")
    export._export_archive = mocker.MagicMock(return_value="")

    export._run_print("mock_archive_dir", ["mock_filepath"])

    export._export_archive.assert_called_once_with("mock_archive_path")
    export._create_archive.assert_called_once_with(
        "mock_archive_dir", "print_archive.sd-export", {"device": "printer"}, ["mock_filepath"]
    )


def test__run_print_raises_ExportError_if_not_empty_string(mocker):
    """
    Ensure ExportError is raised if _run_print returns anything other than ''.
    """
    export = Export()
    export._create_archive = mocker.MagicMock(return_value="mock_archive_path")
    export._export_archive = mocker.MagicMock(return_value="SOMETHING_OTHER_THAN_EMPTY_STRING")

    with pytest.raises(ExportError):
        export._run_print("mock_archive_dir", ["mock_filepath"])


def test_send_file_to_usb_device(mocker):
    """
    Ensure TemporaryDirectory is used when creating and sending the archive containing the export
    file and that the success signal is emitted.
    """
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.service.TemporaryDirectory", return_value=mock_temp_dir)
    export = Export()
    export_usb_call_success_emissions = QSignalSpy(export.export_usb_call_success)
    assert export_usb_call_success_emissions.isValid()
    export_completed_emissions = QSignalSpy(export.export_completed)
    assert export_completed_emissions.isValid()
    _run_disk_export = mocker.patch.object(export, "_run_disk_export")
    mocker.patch("os.path.exists", return_value=True)

    export.send_file_to_usb_device(["path1", "path2"], "mock passphrase")

    _run_disk_export.assert_called_once_with("mock_temp_dir", ["path1", "path2"], "mock passphrase")
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
    export = Export()
    export_usb_call_failure_emissions = QSignalSpy(export.export_usb_call_failure)
    assert export_usb_call_failure_emissions.isValid()
    export_completed_emissions = QSignalSpy(export.export_completed)
    assert export_completed_emissions.isValid()
    error = ExportError("[mock_filepath]")
    _run_disk_export = mocker.patch.object(export, "_run_disk_export", side_effect=error)
    mocker.patch("os.path.exists", return_value=True)

    export.send_file_to_usb_device(["path1", "path2"], "mock passphrase")

    _run_disk_export.assert_called_once_with("mock_temp_dir", ["path1", "path2"], "mock passphrase")
    assert len(export_usb_call_failure_emissions) == 1
    assert export_usb_call_failure_emissions[0] == [error]
    assert len(export_completed_emissions) == 1
    assert export_completed_emissions[0] == [["path1", "path2"]]


def test_run_preflight_checks(mocker):
    """
    Ensure TemporaryDirectory is used when creating and sending the archives during the preflight
    checks and that the success signal is emitted by Export.
    """
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.service.TemporaryDirectory", return_value=mock_temp_dir)
    export = Export()
    preflight_check_call_success_emissions = QSignalSpy(export.preflight_check_call_success)
    assert preflight_check_call_success_emissions.isValid()
    _run_usb_export = mocker.patch.object(export, "_run_usb_test")
    _run_disk_export = mocker.patch.object(export, "_run_disk_test")

    export.run_preflight_checks()

    _run_usb_export.assert_called_once_with("mock_temp_dir")
    _run_disk_export.assert_called_once_with("mock_temp_dir")
    assert len(preflight_check_call_success_emissions) == 1
    assert preflight_check_call_success_emissions[0] == []


def test_run_preflight_checks_error(mocker):
    """
    Ensure TemporaryDirectory is used when creating and sending the archives during the preflight
    checks and that the failure signal is emitted by Export.
    """
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.service.TemporaryDirectory", return_value=mock_temp_dir)
    export = Export()
    preflight_check_call_failure_emissions = QSignalSpy(export.preflight_check_call_failure)
    assert preflight_check_call_failure_emissions.isValid()
    error = ExportError("bang!")
    _run_usb_export = mocker.patch.object(export, "_run_usb_test")
    _run_disk_export = mocker.patch.object(export, "_run_disk_test", side_effect=error)

    export.run_preflight_checks()

    _run_usb_export.assert_called_once_with("mock_temp_dir")
    _run_disk_export.assert_called_once_with("mock_temp_dir")
    assert len(preflight_check_call_failure_emissions) == 1
    assert preflight_check_call_failure_emissions[0] == [error]


def test__run_disk_export(mocker):
    """
    Ensure _export_archive and _create_archive are called with the expected parameters,
    _export_archive is called with the return value of _create_archive, and
    _run_disk_test returns without error if '' is the output status of _export_archive.
    """
    export = Export()
    export._create_archive = mocker.MagicMock(return_value="mock_archive_path")
    export._export_archive = mocker.MagicMock(return_value="")

    export._run_disk_export("mock_archive_dir", ["mock_filepath"], "mock_passphrase")

    export._export_archive.assert_called_once_with("mock_archive_path")
    export._create_archive.assert_called_once_with(
        "mock_archive_dir",
        "archive.sd-export",
        {"encryption_key": "mock_passphrase", "device": "disk", "encryption_method": "luks"},
        ["mock_filepath"],
    )


def test__run_disk_export_raises_ExportError_if_not_empty_string(mocker):
    """
    Ensure ExportError is raised if _run_disk_test returns anything other than ''.
    """
    export = Export()
    export._create_archive = mocker.MagicMock(return_value="mock_archive_path")
    export._export_archive = mocker.MagicMock(return_value="SOMETHING_OTHER_THAN_EMPTY_STRING")

    with pytest.raises(ExportError):
        export._run_disk_export("mock_archive_dir", ["mock_filepath"], "mock_passphrase")


def test__run_disk_test(mocker):
    """
    Ensure _export_archive and _create_archive are called with the expected parameters,
    _export_archive is called with the return value of _create_archive, and
    _run_disk_test returns without error if 'USB_ENCRYPTED' is the output status of _export_archive.
    """
    export = Export()
    export._create_archive = mocker.MagicMock(return_value="mock_archive_path")
    export._export_archive = mocker.MagicMock(return_value=ExportStatus("USB_ENCRYPTED"))

    export._run_disk_test("mock_archive_dir")

    export._export_archive.assert_called_once_with("mock_archive_path")
    export._create_archive.assert_called_once_with(
        "mock_archive_dir", "disk-test.sd-export", {"device": "disk-test"}
    )


def test__run_disk_test_raises_ExportError_if_not_USB_ENCRYPTED(mocker):
    """
    Ensure ExportError is raised if _run_disk_test returns anything other than 'USB_ENCRYPTED'.
    """
    export = Export()
    export._create_archive = mocker.MagicMock(return_value="mock_archive_path")
    export._export_archive = mocker.MagicMock(return_value="SOMETHING_OTHER_THAN_USB_ENCRYPTED")

    with pytest.raises(ExportError):
        export._run_disk_test("mock_archive_dir")


def test__run_usb_test(mocker):
    """
    Ensure _export_archive and _create_archive are called with the expected parameters,
    _export_archive is called with the return value of _create_archive, and
    _run_disk_test returns without error if 'USB_CONNECTED' is the return value of _export_archive.
    """
    export = Export()
    export._create_archive = mocker.MagicMock(return_value="mock_archive_path")
    export._export_archive = mocker.MagicMock(return_value=ExportStatus("USB_CONNECTED"))

    export._run_usb_test("mock_archive_dir")

    export._export_archive.assert_called_once_with("mock_archive_path")
    export._create_archive.assert_called_once_with(
        "mock_archive_dir", "usb-test.sd-export", {"device": "usb-test"}
    )


def test__run_usb_test_raises_ExportError_if_not_USB_CONNECTED(mocker):
    """
    Ensure ExportError is raised if _run_disk_test returns anything other than 'USB_CONNECTED'.
    """
    export = Export()
    export._create_archive = mocker.MagicMock(return_value="mock_archive_path")
    export._export_archive = mocker.MagicMock(return_value="SOMETHING_OTHER_THAN_USB_CONNECTED")

    with pytest.raises(ExportError):
        export._run_usb_test("mock_archive_dir")


def test__create_archive(mocker):
    """
    Ensure _create_archive creates an archive in the supplied directory.
    """
    export = Export()
    archive_path = None
    with TemporaryDirectory() as temp_dir:
        archive_path = export._create_archive(temp_dir, "mock.sd-export", {})
        assert archive_path == os.path.join(temp_dir, "mock.sd-export")
        assert os.path.exists(archive_path)  # sanity check

    assert not os.path.exists(archive_path)


def test__create_archive_with_an_export_file(mocker):
    export = Export()
    archive_path = None
    with TemporaryDirectory() as temp_dir, NamedTemporaryFile() as export_file:
        archive_path = export._create_archive(temp_dir, "mock.sd-export", {}, [export_file.name])
        assert archive_path == os.path.join(temp_dir, "mock.sd-export")
        assert os.path.exists(archive_path)  # sanity check

    assert not os.path.exists(archive_path)


def test__create_archive_with_multiple_export_files(mocker):
    """
    Ensure an archive
    """
    export = Export()
    archive_path = None
    with TemporaryDirectory() as temp_dir, NamedTemporaryFile() as export_file_one, NamedTemporaryFile() as export_file_two:  # noqa
        archive_path = export._create_archive(
            temp_dir, "mock.sd-export", {}, [export_file_one.name, export_file_two.name]
        )
        assert archive_path == os.path.join(temp_dir, "mock.sd-export")
        assert os.path.exists(archive_path)  # sanity check

    assert not os.path.exists(archive_path)


def test__export_archive(mocker):
    """
    Ensure the subprocess call returns the expected output.
    """
    export = Export()
    mocker.patch("subprocess.check_output", return_value=b"USB_CONNECTED")
    status = export._export_archive("mock.sd-export")
    assert status == ExportStatus.USB_CONNECTED

    mocker.patch("subprocess.check_output", return_value=b"mock")
    with pytest.raises(ExportError, match="UNEXPECTED_RETURN_STATUS"):
        export._export_archive("mock.sd-export")


def test__export_archive_does_not_raise_ExportError_when_CalledProcessError(mocker):
    """
    Ensure ExportError is raised if a CalledProcessError is encountered.
    """
    mock_error = subprocess.CalledProcessError(cmd=["mock_cmd"], returncode=123)
    mocker.patch("subprocess.check_output", side_effect=mock_error)

    export = Export()

    with pytest.raises(ExportError, match="CALLED_PROCESS_ERROR"):
        export._export_archive("mock.sd-export")


def test__export_archive_with_evil_command(mocker):
    """
    Ensure shell command is shell-escaped.
    """
    export = Export()
    check_output = mocker.patch("subprocess.check_output", return_value=b"ERROR_FILE_NOT_FOUND")

    with pytest.raises(ExportError, match="UNEXPECTED_RETURN_STATUS"):
        export._export_archive("somefile; rm -rf ~")

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
    export = Export()
    check_output = mocker.patch("subprocess.check_output", return_value=b"")

    result = export._export_archive("somefile.sd-export")

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
