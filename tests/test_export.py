import os
import subprocess
from tempfile import NamedTemporaryFile, TemporaryDirectory

import pytest

from securedrop_client.export import Export, ExportError, ExportStatus


def test_run_printer_preflight(mocker):
    """
    Ensure TemporaryDirectory is used when creating and sending the archives during the preflight
    checks and that the success signal is emitted by Export.
    """
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.TemporaryDirectory", return_value=mock_temp_dir)
    export = Export()
    export.printer_preflight_success = mocker.MagicMock()
    export.printer_preflight_success.emit = mocker.MagicMock()
    _run_printer_preflight = mocker.patch.object(export, "_run_printer_preflight")

    export.run_printer_preflight()

    _run_printer_preflight.assert_called_once_with("mock_temp_dir")
    export.printer_preflight_success.emit.assert_called_once_with()


def test_run_printer_preflight_error(mocker):
    """
    Ensure TemporaryDirectory is used when creating and sending the archives during the preflight
    checks and that the failure signal is emitted by Export.
    """
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.TemporaryDirectory", return_value=mock_temp_dir)
    export = Export()
    export.printer_preflight_failure = mocker.MagicMock()
    export.printer_preflight_failure.emit = mocker.MagicMock()
    error = ExportError("bang!")
    _run_print_preflight = mocker.patch.object(export, "_run_printer_preflight", side_effect=error)

    export.run_printer_preflight()

    _run_print_preflight.assert_called_once_with("mock_temp_dir")
    export.printer_preflight_failure.emit.assert_called_once_with(error)


def test__run_printer_preflight(mocker):
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


def test__run_printer_preflight_raises_ExportError_if_not_empty_string(mocker):
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
    mocker.patch("securedrop_client.export.TemporaryDirectory", return_value=mock_temp_dir)
    export = Export()
    export.print_call_success = mocker.MagicMock()
    export.print_call_success.emit = mocker.MagicMock()
    export.export_completed = mocker.MagicMock()
    export.export_completed.emit = mocker.MagicMock()
    _run_print = mocker.patch.object(export, "_run_print")
    mocker.patch("os.path.exists", return_value=True)

    export.print(["path1", "path2"])

    _run_print.assert_called_once_with("mock_temp_dir", ["path1", "path2"])
    export.print_call_success.emit.assert_called_once_with()
    export.export_completed.emit.assert_called_once_with(["path1", "path2"])


def test_print_error(mocker):
    """
    Ensure TemporaryDirectory is used when creating and sending the archive containing the file to
    print and that the failure signal is emitted.
    """
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.TemporaryDirectory", return_value=mock_temp_dir)
    export = Export()
    export.print_call_failure = mocker.MagicMock()
    export.print_call_failure.emit = mocker.MagicMock()
    export.export_completed = mocker.MagicMock()
    export.export_completed.emit = mocker.MagicMock()
    error = ExportError("[mock_filepath]")
    _run_print = mocker.patch.object(export, "_run_print", side_effect=error)
    mocker.patch("os.path.exists", return_value=True)

    export.print(["path1", "path2"])

    _run_print.assert_called_once_with("mock_temp_dir", ["path1", "path2"])
    export.print_call_failure.emit.assert_called_once_with(error)
    export.export_completed.emit.assert_called_once_with(["path1", "path2"])


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
    mocker.patch("securedrop_client.export.TemporaryDirectory", return_value=mock_temp_dir)
    export = Export()
    export.export_usb_call_success = mocker.MagicMock()
    export.export_usb_call_success.emit = mocker.MagicMock()
    export.export_completed = mocker.MagicMock()
    export.export_completed.emit = mocker.MagicMock()
    _run_disk_export = mocker.patch.object(export, "_run_disk_export")
    mocker.patch("os.path.exists", return_value=True)

    export.send_file_to_usb_device(["path1", "path2"], "mock passphrase")

    _run_disk_export.assert_called_once_with("mock_temp_dir", ["path1", "path2"], "mock passphrase")
    export.export_usb_call_success.emit.assert_called_once_with()
    export.export_completed.emit.assert_called_once_with(["path1", "path2"])


def test_send_file_to_usb_device_error(mocker):
    """
    Ensure TemporaryDirectory is used when creating and sending the archive containing the export
    file and that the failure signal is emitted.
    """
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.TemporaryDirectory", return_value=mock_temp_dir)
    export = Export()
    export.export_usb_call_failure = mocker.MagicMock()
    export.export_usb_call_failure.emit = mocker.MagicMock()
    export.export_completed = mocker.MagicMock()
    export.export_completed.emit = mocker.MagicMock()
    error = ExportError("[mock_filepath]")
    _run_disk_export = mocker.patch.object(export, "_run_disk_export", side_effect=error)
    mocker.patch("os.path.exists", return_value=True)

    export.send_file_to_usb_device(["path1", "path2"], "mock passphrase")

    _run_disk_export.assert_called_once_with("mock_temp_dir", ["path1", "path2"], "mock passphrase")
    export.export_usb_call_failure.emit.assert_called_once_with(error)
    export.export_completed.emit.assert_called_once_with(["path1", "path2"])


def test_run_preflight_checks(mocker):
    """
    Ensure TemporaryDirectory is used when creating and sending the archives during the preflight
    checks and that the success signal is emitted by Export.
    """
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.TemporaryDirectory", return_value=mock_temp_dir)
    export = Export()
    export.preflight_check_call_success = mocker.MagicMock()
    export.preflight_check_call_success.emit = mocker.MagicMock()
    _run_usb_export = mocker.patch.object(export, "_run_usb_test")
    _run_disk_export = mocker.patch.object(export, "_run_disk_test")

    export.run_preflight_checks()

    _run_usb_export.assert_called_once_with("mock_temp_dir")
    _run_disk_export.assert_called_once_with("mock_temp_dir")
    export.preflight_check_call_success.emit.assert_called_once_with()


def test_run_preflight_checks_error(mocker):
    """
    Ensure TemporaryDirectory is used when creating and sending the archives during the preflight
    checks and that the failure signal is emitted by Export.
    """
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.TemporaryDirectory", return_value=mock_temp_dir)
    export = Export()
    export.preflight_check_call_failure = mocker.MagicMock()
    export.preflight_check_call_failure.emit = mocker.MagicMock()
    error = ExportError("bang!")
    _run_usb_export = mocker.patch.object(export, "_run_usb_test")
    _run_disk_export = mocker.patch.object(export, "_run_disk_test", side_effect=error)

    export.run_preflight_checks()

    _run_usb_export.assert_called_once_with("mock_temp_dir")
    _run_disk_export.assert_called_once_with("mock_temp_dir")
    export.preflight_check_call_failure.emit.assert_called_once_with(error)


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
    check_output = mocker.patch("subprocess.check_output", return_value=b"")

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
