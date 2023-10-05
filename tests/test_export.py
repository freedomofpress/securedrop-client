import os
import subprocess
import unittest
from tempfile import NamedTemporaryFile, TemporaryDirectory

import pytest

from securedrop_client import export
from securedrop_client.export import Export, ExportError, ExportStatus


class TestService(unittest.TestCase):
    def tearDown(self):
        # ensure any changes to the export.Service instance are reset
        # export.resetService()
        pass

    def test_service_is_unique(self):
        service = export.getService()
        same_service = export.getService()  # Act.

        self.assertTrue(
            service is same_service,
            "expected successive calls to getService to return the same service, got different services",  # noqa: E501
        )

    def test_service_can_be_reset(self):
        service = export.getService()
        export.resetService()  # Act.
        different_service = export.getService()

        self.assertTrue(
            different_service is not service,
            "expected resetService to reset the service, got same service after reset",
        )


def test_run_printer_preflight(mocker):
    """
    Ensure TemporaryDirectory is used when creating and sending the archives during the preflight
    checks and that the success signal is emitted by Export.
    """

    export = Export()
    mocker.patch.object(
        export, "_build_archive_and_export", return_value=ExportStatus.PREFLIGHT_SUCCESS
    )
    export.printer_preflight_success = mocker.MagicMock()
    export.printer_preflight_success.emit = mocker.MagicMock()

    export.run_printer_preflight()
    export.printer_preflight_success.emit.assert_called_once_with()


def test_run_printer_preflight_error(mocker):
    """
    Ensure TemporaryDirectory is used when creating and sending the archives during the preflight
    checks and that the failure signal is emitted by Export.
    """

    export = Export()
    error = ExportError("bang!")
    mocker.patch.object(export, "_build_archive_and_export", side_effect=error)

    export.printer_preflight_failure = mocker.MagicMock()
    export.printer_preflight_failure.emit = mocker.MagicMock()

    export.run_printer_preflight()

    export.printer_preflight_failure.emit.assert_called_once_with(error)


def test_print(mocker):
    export = Export()

    mock_qrexec_call = mocker.patch.object(
        export, "_build_archive_and_export", return_value=ExportStatus.PRINT_SUCCESS
    )

    export.print_call_success = mocker.MagicMock()
    export.print_call_success.emit = mocker.MagicMock()
    export.export_completed = mocker.MagicMock()
    export.export_completed.emit = mocker.MagicMock()

    export.print(["path1", "path2"])

    mock_qrexec_call.assert_called_once_with(
        metadata=export.PRINT_METADATA, filename=export.PRINT_FN, filepaths=["path1", "path2"]
    )
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
    error = ExportError("oh no!")
    _run_print = mocker.patch.object(export, "_build_archive_and_export", side_effect=error)
    mocker.patch("os.path.exists", return_value=True)

    export.print(["path1", "path2"])

    _run_print.assert_called_once_with(
        metadata=export.PRINT_METADATA, filename=export.PRINT_FN, filepaths=["path1", "path2"]
    )
    export.print_call_failure.emit.assert_called_once_with(error)
    export.export_completed.emit.assert_called_once_with(["path1", "path2"])


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
    _run_disk_export = mocker.patch.object(export, "_build_archive_and_export")
    mocker.patch("os.path.exists", return_value=True)

    metadata = export.DISK_METADATA
    metadata[export.DISK_ENCRYPTION_KEY_NAME] = "mock passphrase"

    export.send_file_to_usb_device(["path1", "path2"], "mock passphrase")

    _run_disk_export.assert_called_once_with(
        metadata=metadata, filename=export.DISK_FN, filepaths=["path1", "path2"]
    )
    export.export_usb_call_success.emit.assert_called_once_with()
    export.export_completed.emit.assert_called_once_with(["path1", "path2"])


def test_send_file_to_usb_device_error(mocker):
    """
    Ensure TemporaryDirectory is used when creating and sending the archive containing the export
    file and that the failure signal is emitted.
    """
    export = Export()

    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.TemporaryDirectory", return_value=mock_temp_dir)

    export.export_usb_call_failure = mocker.MagicMock()
    export.export_usb_call_failure.emit = mocker.MagicMock()
    export.export_completed = mocker.MagicMock()
    export.export_completed.emit = mocker.MagicMock()
    error = ExportError("ohno")
    _run_disk_export = mocker.patch.object(export, "_build_archive_and_export", side_effect=error)

    metadata = export.DISK_METADATA
    metadata[export.DISK_ENCRYPTION_KEY_NAME] = "mock passphrase"

    export.send_file_to_usb_device(["path1", "path2"], "mock passphrase")

    _run_disk_export.assert_called_once_with(
        metadata=metadata, filename=export.DISK_FN, filepaths=["path1", "path2"]
    )
    export.export_usb_call_failure.emit.assert_called_once_with(error)
    export.export_completed.emit.assert_called_once_with(["path1", "path2"])


def test_run_usb_preflight_checks(mocker):
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
    _run_export = mocker.patch.object(export, "_build_archive_and_export")

    export.run_preflight_checks()

    _run_export.assert_called_once_with(
        metadata=export.USB_TEST_METADATA, filename=export.USB_TEST_FN
    )
    export.preflight_check_call_success.emit.assert_called_once_with()


def test_run_usb_preflight_checks_error(mocker):
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
    _run_export = mocker.patch.object(export, "_build_archive_and_export", side_effect=error)

    export.run_preflight_checks()

    _run_export.assert_called_once_with(
        metadata=export.USB_TEST_METADATA, filename=export.USB_TEST_FN
    )
    export.preflight_check_call_failure.emit.assert_called_once_with(error)


@pytest.mark.parametrize("success_qrexec", [e.value for e in ExportStatus])
def test__build_archive_and_export_success(mocker, success_qrexec):
    """
    Test the command that calls out to underlying qrexec service.
    """
    export = Export()

    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.TemporaryDirectory", return_value=mock_temp_dir)

    mock_qrexec_call = mocker.patch.object(
        export, "_run_qrexec_export", return_value=bytes(success_qrexec, "utf-8")
    )
    mocker.patch.object(export, "_create_archive", return_value="mock_archive_path")

    metadata = {"device": "pretend", "encryption_method": "transparent"}

    result = export._build_archive_and_export(
        metadata=metadata, filename="mock_filename", filepaths=["mock_filepath"]
    )
    mock_qrexec_call.assert_called_once()

    assert result == bytes(success_qrexec, "utf-8")


def test__build_archive_and_export_error(mocker):
    """
    Test the command that calls out to underlying qrexec service.
    """
    export = Export()
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value="mock_temp_dir")
    mocker.patch("securedrop_client.export.TemporaryDirectory", return_value=mock_temp_dir)

    mocker.patch.object(export, "_create_archive", return_value="mock_archive_path")

    mock_qrexec_call = mocker.patch.object(
        export, "_run_qrexec_export", side_effect=ExportError(ExportStatus.UNEXPECTED_RETURN_STATUS)
    )

    metadata = {"device": "pretend", "encryption_method": "transparent"}

    with pytest.raises(ExportError):
        result = export._build_archive_and_export(
            metadata=metadata, filename="mock_filename", filepaths=["mock_filepath"]
        )
        assert result == ExportStatus.UNEXPECTED_RETURN_STATUS

    mock_qrexec_call.assert_called_once()


def test__create_archive(mocker):
    """
    Ensure _create_archive creates an archive in the supplied directory.
    """
    export = Export()
    archive_path = None
    with TemporaryDirectory() as temp_dir:
        archive_path = export._create_archive(
            archive_dir=temp_dir, archive_fn="mock.sd-export", metadata={}, filepaths=[]
        )
        assert archive_path == os.path.join(temp_dir, "mock.sd-export")
        assert os.path.exists(archive_path)  # sanity check

    assert not os.path.exists(archive_path)


def test__create_archive_with_an_export_file(mocker):
    export = Export()
    archive_path = None
    with TemporaryDirectory() as temp_dir, NamedTemporaryFile() as export_file:
        archive_path = export._create_archive(
            archive_dir=temp_dir,
            archive_fn="mock.sd-export",
            metadata={},
            filepaths=[export_file.name],
        )
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
        transcript_path = os.path.join(temp_dir, "transcript.txt")
        with open(transcript_path, "a+") as transcript:
            archive_path = export._create_archive(
                temp_dir,
                "mock.sd-export",
                {},
                [export_file_one.name, export_file_two.name, transcript.name],
            )
            assert archive_path == os.path.join(temp_dir, "mock.sd-export")
            assert os.path.exists(archive_path)  # sanity check

    assert not os.path.exists(archive_path)


@pytest.mark.parametrize("qrexec_return_value_success", [e.value for e in ExportStatus])
def test__run_qrexec_export(mocker, qrexec_return_value_success):
    """
    Ensure the subprocess call returns the expected output.
    """
    export = Export()
    qrexec_mocker = mocker.patch(
        "subprocess.check_output", return_value=bytes(qrexec_return_value_success, "utf-8")
    )
    result = export._run_qrexec_export("mock.sd-export")

    qrexec_mocker.assert_called_once_with(
        [
            "qrexec-client-vm",
            "--",
            "sd-devices",
            "qubes.OpenInVM",
            "/usr/lib/qubes/qopen-in-vm",
            "--view-only",
            "--",
            "mock.sd-export",
        ],
        stderr=-2,
    )

    assert ExportStatus(result)


@pytest.mark.parametrize(
    "qrexec_return_value_error", [b"", b"qrexec not connected", b"DEVICE_UNLOCKED\nERROR_WRITE"]
)
def test__run_qrexec_export_returns_bad_data(mocker, qrexec_return_value_error):
    """
    Ensure the subprocess call returns the expected output.
    """
    export = Export()
    qrexec_mocker = mocker.patch("subprocess.check_output", return_value=qrexec_return_value_error)

    with pytest.raises(ExportError, match="UNEXPECTED_RETURN_STATUS"):
        export._run_qrexec_export("mock.sd-export")

    qrexec_mocker.assert_called_once_with(
        [
            "qrexec-client-vm",
            "--",
            "sd-devices",
            "qubes.OpenInVM",
            "/usr/lib/qubes/qopen-in-vm",
            "--view-only",
            "--",
            "mock.sd-export",
        ],
        stderr=-2,
    )


def test__run_qrexec_export_does_not_raise_ExportError_when_CalledProcessError(mocker):
    """
    Ensure ExportError is raised if a CalledProcessError is encountered.
    """
    mock_error = subprocess.CalledProcessError(cmd=["mock_cmd"], returncode=123)
    mocker.patch("subprocess.check_output", side_effect=mock_error)

    export = Export()

    with pytest.raises(ExportError, match="CALLED_PROCESS_ERROR"):
        export._run_qrexec_export("mock.sd-export")


def test__run_qrexec_export_with_evil_command(mocker):
    """
    Ensure shell command is shell-escaped.
    """
    export = Export()
    check_output = mocker.patch("subprocess.check_output", return_value=b"ERROR_FILE_NOT_FOUND")

    with pytest.raises(ExportError, match="UNEXPECTED_RETURN_STATUS"):
        export._run_qrexec_export("somefile; ls -la ~")

    check_output.assert_called_once_with(
        [
            "qrexec-client-vm",
            "--",
            "sd-devices",
            "qubes.OpenInVM",
            "/usr/lib/qubes/qopen-in-vm",
            "--view-only",
            "--",
            "'somefile; ls -la ~'",
        ],
        stderr=-2,
    )


def test__run_qrexec_export_error_on_empty_return_value(mocker):
    """
    Ensure an error is raised when qrexec call returns empty string,
    """
    export = Export()
    check_output = mocker.patch("subprocess.check_output", return_value=b"")

    with pytest.raises(ExportError, match="UNEXPECTED_RETURN_STATUS"):
        export._run_qrexec_export("somefile.sd-export")

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
