import os
import pytest
from securedrop_client.export_status import ExportError, ExportStatus

from securedrop_client.gui.conversation.export import Device
from securedrop_client.logic import Controller
import subprocess
import tarfile
from tests import factory
from tempfile import NamedTemporaryFile, TemporaryDirectory
from unittest import mock

_PATH_TO_PRETEND_ARCHIVE = "/tmp/archive-pretend"
_QREXEC_EXPORT_COMMAND = [
    "qrexec-client-vm",
    "--",
    "sd-devices",
    "qubes.OpenInVM",
    "/usr/lib/qubes/qopen-in-vm",
    "--view-only",
    "--",
    f"{_PATH_TO_PRETEND_ARCHIVE}",
]
_MOCK_TMPDIR = "/tmp/mock_tmpdir"


@mock.patch("subprocess.check_output")
class TestDevice:
    @classmethod
    def setup_class(cls):
        mock_get_file = mock.MagicMock()
        cls.mock_controller = mock.MagicMock(spec=Controller)
        cls.mock_controller.data_dir = "pretend-data-dir"
        cls.mock_controller.get_file = mock_get_file
        cls.device = Device(cls.mock_controller)

    # Reset any manually-changed mock controller values before next test
    @classmethod
    def setup_method(cls):
        cls.mock_file = factory.File(source=factory.Source())
        cls.mock_controller.get_file.return_value = cls.mock_file
        cls.mock_controller.downloaded_file_exists.return_value = True
        cls.device._create_archive = mock.MagicMock()
        cls.device._create_archive.return_value = _PATH_TO_PRETEND_ARCHIVE
        cls.mock_tmpdir = mock.MagicMock()
        cls.mock_tmpdir.__enter__ = mock.MagicMock(return_value=_MOCK_TMPDIR)

    @classmethod
    def teardown_method(cls):
        cls.mock_file = None
        cls.mock_controller.get_file.return_value = None
        cls.device._create_archive = None

    def test_Device_run_printer_preflight_checks(self, mock_subprocess):
        with mock.patch(
            "securedrop_client.gui.conversation.export.device.TemporaryDirectory",
            return_value=self.mock_tmpdir,
        ):
            self.device.run_printer_preflight_checks()

        mock_subprocess.assert_called_once()
        assert (
            _QREXEC_EXPORT_COMMAND in mock_subprocess.call_args[0]
        ), f"Actual: {mock_subprocess.call_args[0]}"

    def test_Device_run_print_preflight_checks_with_error(self, mock_sp):
        with mock.patch.object(
            self.device,
            "_build_archive_and_export",
            side_effect=ExportError(ExportStatus.ERROR_PRINTER_NOT_SUPPORTED),
        ), mock.patch(
            "securedrop_client.gui.conversation.export.device.logger.error"
        ) as err, pytest.raises(
            ExportError
        ) as e:
            self.device.run_export_preflight_checks()

        err.assert_called_once_with("Print preflight failed")

    def test_Device_run_print_file(self, mock_subprocess):
        file = self.mock_file
        with mock.patch(
            "securedrop_client.gui.conversation.export.device.TemporaryDirectory",
            return_value=self.mock_tmpdir,
        ):
            self.device.print_file(file.uuid)

        filepath = file.location(self.mock_controller.data_dir)

        self.device._create_archive.assert_called_once_with(
            archive_dir=_MOCK_TMPDIR,
            archive_fn=self.device._PRINT_FN,
            metadata=self.device._PRINT_METADATA,
            filepaths=[filepath],
        )
        mock_subprocess.assert_called_once()
        assert _QREXEC_EXPORT_COMMAND in mock_subprocess.call_args[0]

    def test_Device_print_transcript(self, mock_subprocess):
        filepath = "some/file/path"

        with mock.patch(
            "securedrop_client.gui.conversation.export.device.TemporaryDirectory",
            return_value=self.mock_tmpdir,
        ):
            self.device.print_transcript(filepath)

        mock_subprocess.assert_called_once()

        self.device._create_archive.assert_called_once_with(
            archive_dir=_MOCK_TMPDIR,
            archive_fn=self.device._PRINT_FN,
            metadata=self.device._PRINT_METADATA,
            filepaths=[filepath],
        )
        mock_subprocess.assert_called_once()
        assert _QREXEC_EXPORT_COMMAND in mock_subprocess.call_args[0]

    def test_Device_print_file_file_missing(self, mock_subprocess, mocker):
        file = self.mock_file
        self.mock_controller.downloaded_file_exists.return_value = False

        warning_logger = mocker.patch(
            "securedrop_client.gui.conversation.export.device.logger.warning"
        )

        self.device.print_file(file.uuid)
        mock_subprocess.assert_not_called()

        path = str(file.location(self.mock_controller.data_dir))
        log_msg = f"Cannot find file in {path}"

        warning_logger.assert_called_once_with(log_msg)

    def test_Device_print_file_when_orig_file_already_exists(self, mock_subprocess):
        file = self.mock_file

        with mock.patch(
            "securedrop_client.gui.conversation.export.device.TemporaryDirectory",
            return_value=self.mock_tmpdir,
        ):
            self.device.print_file(file.uuid)

        self.mock_controller.get_file.assert_called_with(file.uuid)
        mock_subprocess.assert_called_once()

        filepath = file.location(self.mock_controller.data_dir)

        self.device._create_archive.assert_called_once_with(
            archive_dir=_MOCK_TMPDIR,
            archive_fn=self.device._PRINT_FN,
            metadata=self.device._PRINT_METADATA,
            filepaths=[filepath],
        )
        mock_subprocess.assert_called_once()
        assert _QREXEC_EXPORT_COMMAND in mock_subprocess.call_args[0]

    def test_Device_run_export_preflight_checks(self, mock_subprocess):
        with mock.patch(
            "securedrop_client.gui.conversation.export.device.TemporaryDirectory",
            return_value=self.mock_tmpdir,
        ):
            self.device.run_export_preflight_checks()
        mock_subprocess.assert_called_once()

        self.device._create_archive.assert_called_once_with(
            archive_dir=_MOCK_TMPDIR,
            archive_fn=self.device._USB_TEST_FN,
            metadata=self.device._USB_TEST_METADATA,
            filepaths=[],
        )
        mock_subprocess.assert_called_once()
        assert _QREXEC_EXPORT_COMMAND in mock_subprocess.call_args[0]

    def test_Device_run_export_preflight_checks_with_error(self, mock_sp):
        with mock.patch.object(
            self.device,
            "_build_archive_and_export",
            side_effect=ExportError(ExportStatus.DEVICE_ERROR),
        ), mock.patch(
            "securedrop_client.gui.conversation.export.device.logger.error"
        ) as err, pytest.raises(
            ExportError
        ) as e:
            self.device.run_export_preflight_checks()

        err.assert_called_once_with("Export preflight failed")

    def test_Device_export_file_to_usb_drive(self, mock_subprocess):
        file = self.mock_file
        passphrase = "mock passphrase"

        with mock.patch(
            "securedrop_client.gui.conversation.export.device.TemporaryDirectory",
            return_value=self.mock_tmpdir,
        ):
            self.device.export_file_to_usb_drive(file.uuid, passphrase)
        mock_subprocess.assert_called_once()

        filepath = file.location(self.mock_controller.data_dir)

        expected_md = self.device._DISK_METADATA.copy()
        expected_md[self.device._DISK_ENCRYPTION_KEY_NAME] = passphrase

        self.device._create_archive.assert_called_once_with(
            archive_dir=_MOCK_TMPDIR,
            archive_fn=self.device._DISK_FN,
            metadata=expected_md,
            filepaths=[filepath],
        )

    def test_Device_export_file_to_usb_drive_file_missing(self, mock_subprocess, mocker):
        file = self.mock_file
        self.mock_controller.downloaded_file_exists.return_value = False

        warning_logger = mocker.patch(
            "securedrop_client.gui.conversation.export.device.logger.warning"
        )
        with mock.patch(
            "securedrop_client.gui.conversation.export.device.TemporaryDirectory",
            return_value=self.mock_tmpdir,
        ):
            self.device.export_file_to_usb_drive(file.uuid, "mock passphrase")

        path = str(file.location(self.mock_controller.data_dir))
        log_msg = f"Cannot find file in {path}"
        warning_logger.assert_called_once_with(log_msg)

        mock_subprocess.assert_not_called()

    def test_Device_export_file_to_usb_drive_when_orig_file_already_exists(self, mock_subprocess):
        file = self.mock_file
        passphrase = "mock passphrase"

        with mock.patch(
            "securedrop_client.gui.conversation.export.device.TemporaryDirectory",
            return_value=self.mock_tmpdir,
        ):
            self.device.export_file_to_usb_drive(file.uuid, passphrase)

        expected_metadata = self.device._DISK_METADATA.copy()
        expected_metadata[self.device._DISK_ENCRYPTION_KEY_NAME] = passphrase
        expected_filepath = file.location(self.mock_controller.data_dir)

        self.mock_controller.get_file.assert_called_with(file.uuid)
        self.device._create_archive.assert_called_once_with(
            archive_dir=_MOCK_TMPDIR,
            archive_fn=self.device._DISK_FN,
            metadata=expected_metadata,
            filepaths=[expected_filepath],
        )

        mock_subprocess.assert_called_once()
        assert _QREXEC_EXPORT_COMMAND in mock_subprocess.call_args[0]

    def test_Device_export_transcript(self, mock_subprocess):
        filepath = "some/file/path"
        passphrase = "passphrase"

        with mock.patch(
            "securedrop_client.gui.conversation.export.device.TemporaryDirectory",
            return_value=self.mock_tmpdir,
        ):
            self.device.export_transcript(filepath, passphrase)

        expected_metadata = self.device._DISK_METADATA.copy()
        expected_metadata[self.device._DISK_ENCRYPTION_KEY_NAME] = passphrase

        self.device._create_archive.assert_called_once_with(
            archive_dir=_MOCK_TMPDIR,
            archive_fn=self.device._DISK_FN,
            metadata=expected_metadata,
            filepaths=[filepath],
        )
        mock_subprocess.assert_called_once()
        assert _QREXEC_EXPORT_COMMAND in mock_subprocess.call_args[0]

    def test_Device_export_files(self, mock_subprocess):
        filepaths = ["some/file/path", "some/other/file/path"]
        passphrase = "Correct-horse-battery-staple!"

        expected_metadata = self.device._DISK_METADATA.copy()
        expected_metadata[self.device._DISK_ENCRYPTION_KEY_NAME] = passphrase

        with mock.patch(
            "securedrop_client.gui.conversation.export.device.TemporaryDirectory",
            return_value=self.mock_tmpdir,
        ):
            self.device.export_files(filepaths, passphrase)

        self.device._create_archive.assert_called_once_with(
            archive_dir=_MOCK_TMPDIR,
            archive_fn=self.device._DISK_FN,
            metadata=expected_metadata,
            filepaths=filepaths,
        )
        mock_subprocess.assert_called_once()
        assert _QREXEC_EXPORT_COMMAND in mock_subprocess.call_args[0]

    @pytest.mark.parametrize("status", [i.value for i in ExportStatus])
    def test__run_qrexec_success(self, mocked_subprocess, status):
        mocked_subprocess.return_value = f"{status}\n".encode("utf-8")
        enum = ExportStatus(status)

        assert self.device._run_qrexec_export(_PATH_TO_PRETEND_ARCHIVE) == enum

    def test__run_qrexec_calledprocess_raises_exportstatus(self, mocked_subprocess):
        mocked_subprocess.side_effect = ValueError(
            "These are not the ExportStatuses you're looking for..."
        )
        with pytest.raises(ExportError) as e:
            self.device._run_qrexec_export(_PATH_TO_PRETEND_ARCHIVE)

        assert e.value.status == ExportStatus.UNEXPECTED_RETURN_STATUS

    def test__run_qrexec_valuerror_raises_exportstatus(self, mocked_subprocess):
        mocked_subprocess.side_effect = subprocess.CalledProcessError(1, "check_output")
        with pytest.raises(ExportError) as e:
            self.device._run_qrexec_export(_PATH_TO_PRETEND_ARCHIVE)

        assert e.value.status == ExportStatus.CALLED_PROCESS_ERROR

    @mock.patch("securedrop_client.gui.conversation.export.device.tarfile")
    def test__add_virtual_file_to_archive(self, mock_tarfile, mock_sp):
        mock_tarinfo = mock.MagicMock(spec=tarfile.TarInfo)
        mock_tarfile.TarInfo.return_value = mock_tarinfo

        self.device._add_virtual_file_to_archive(
            mock_tarfile, "mock_file", {"test_filedata": "lgtm"}
        )

        mock_tarfile.TarInfo.assert_called_once()

    def test__create_archive(self, mocker):
        """
        Ensure _create_archive creates an archive in the supplied directory.
        """
        # A Device where we don't mock out the tempfile
        device = Device(self.mock_controller)
        archive_path = None
        filepaths = [_PATH_TO_PRETEND_ARCHIVE]
        with TemporaryDirectory() as temp_dir:
            archive_path = device._create_archive(temp_dir, "mock.sd-export", {}, filepaths)
            assert archive_path == os.path.join(temp_dir, "mock.sd-export")
            assert os.path.exists(archive_path)  # sanity check

        assert not os.path.exists(archive_path)

    def test__create_archive_with_an_export_file(self, mocker):
        device = Device(self.mock_controller)
        archive_path = None
        with TemporaryDirectory() as temp_dir, NamedTemporaryFile() as export_file:
            archive_path = device._create_archive(
                temp_dir, "mock.sd-export", {}, [export_file.name]
            )
            assert archive_path == os.path.join(temp_dir, "mock.sd-export")
            assert os.path.exists(archive_path)  # sanity check

        assert not os.path.exists(archive_path)

    def test__create_archive_with_multiple_export_files(self, mocker):
        device = Device(self.mock_controller)
        archive_path = None
        with TemporaryDirectory() as temp_dir, NamedTemporaryFile() as export_file_one, NamedTemporaryFile() as export_file_two:
            transcript_path = os.path.join(temp_dir, "transcript.txt")
            with open(transcript_path, "a+") as transcript:
                archive_path = device._create_archive(
                    temp_dir,
                    "mock.sd-export",
                    {},
                    [export_file_one.name, export_file_two.name, transcript.name],
                )
                assert archive_path == os.path.join(temp_dir, "mock.sd-export")
                assert os.path.exists(archive_path)  # sanity check

        assert not os.path.exists(archive_path)
