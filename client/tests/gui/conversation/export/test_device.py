import os
import subprocess
import tarfile
from tempfile import NamedTemporaryFile, TemporaryDirectory
from unittest import mock

import pytest

from securedrop_client.export_status import ExportError, ExportStatus
from securedrop_client.gui.conversation.export import Device
from tests import factory

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
_MOCK_FILEDIR = "/tmp/mock_tmpdir/"


@mock.patch("subprocess.check_output")
class TestDevice:
    @classmethod
    def setup_class(cls):
        cls.device = None

    # Reset any manually-changed mock values before next test
    @classmethod
    def setup_method(cls):
        cls.mock_file = factory.File(source=factory.Source())
        cls.mock_file_location = f"{_MOCK_FILEDIR}{cls.mock_file.filename}"
        cls.device = Device()
        cls.device._create_archive = mock.MagicMock()
        cls.device._create_archive.return_value = _PATH_TO_PRETEND_ARCHIVE
        cls.mock_tmpdir = mock.MagicMock()
        cls.mock_tmpdir.__enter__ = mock.MagicMock(return_value=_MOCK_FILEDIR)

    @classmethod
    def teardown_method(cls):
        cls.mock_file = None
        cls.device._create_archive = None

    def test_Device_run_printer_preflight_checks(self, mock_subprocess):
        device = Device()
        device._create_archive = mock.MagicMock()
        device._create_archive.return_value = _PATH_TO_PRETEND_ARCHIVE

        with mock.patch(
            "securedrop_client.gui.conversation.export.device.TemporaryDirectory",
            return_value=self.mock_tmpdir,
        ):
            device.run_printer_preflight_checks()

        mock_subprocess.assert_called_once()
        assert (
            _QREXEC_EXPORT_COMMAND in mock_subprocess.call_args[0]
        ), f"Actual: {mock_subprocess.call_args[0]}"

    def test_Device_run_print_preflight_checks_with_error(self, mock_sp):
        mock_sp.side_effect = subprocess.CalledProcessError(1, "check_output")

        with mock.patch("securedrop_client.gui.conversation.export.device.logger.error") as err:
            self.device.run_printer_preflight_checks()

        assert "Print preflight failed" in err.call_args[0]

    def test_Device_print(self, mock_subprocess):
        with mock.patch(
            "securedrop_client.gui.conversation.export.device.TemporaryDirectory",
            return_value=self.mock_tmpdir,
        ):
            self.device.print([self.mock_file_location])

        self.device._create_archive.assert_called_once_with(
            archive_dir=_MOCK_FILEDIR,
            archive_fn=self.device._PRINT_FN,
            metadata=self.device._PRINT_METADATA,
            filepaths=[self.mock_file_location],
        )
        mock_subprocess.assert_called_once()
        assert _QREXEC_EXPORT_COMMAND in mock_subprocess.call_args[0]

    def test_Device_print_file_file_missing(self, mock_subprocess, mocker):
        device = Device()
        warning_logger = mocker.patch(
            "securedrop_client.gui.conversation.export.device.logger.warning"
        )

        log_msg = "File not found at specified filepath, skipping"

        device.print("some-missing-file-uuid")

        assert log_msg in warning_logger.call_args[0]
        mock_subprocess.assert_not_called()

    def test_Device_run_export_preflight_checks(self, mock_subprocess):
        with mock.patch(
            "securedrop_client.gui.conversation.export.device.TemporaryDirectory",
            return_value=self.mock_tmpdir,
        ):
            self.device.run_export_preflight_checks()
        mock_subprocess.assert_called_once()

        self.device._create_archive.assert_called_once_with(
            archive_dir=_MOCK_FILEDIR,
            archive_fn=self.device._USB_TEST_FN,
            metadata=self.device._USB_TEST_METADATA,
        )
        mock_subprocess.assert_called_once()
        assert _QREXEC_EXPORT_COMMAND in mock_subprocess.call_args[0]

    def test_Device_run_export_preflight_checks_with_error(self, mock_sp):
        mock_sp.side_effect = subprocess.CalledProcessError(1, "check_output")

        with mock.patch("securedrop_client.gui.conversation.export.device.logger.error") as err:
            self.device.run_export_preflight_checks()

        assert "Export preflight failed" in err.call_args[0]

    def test_Device_export_file_missing(self, mock_subprocess, mocker):
        device = Device()

        warning_logger = mocker.patch(
            "securedrop_client.gui.conversation.export.device.logger.warning"
        )
        with mock.patch(
            "securedrop_client.gui.conversation.export.device.tarfile.open",
            return_value=mock.MagicMock(),
        ), mock.patch(
            "securedrop_client.gui.conversation.export.device.TemporaryDirectory",
            return_value=self.mock_tmpdir,
        ):
            device.export(["/not/a/real/location"], "mock passphrase")

        warning_logger.assert_called_once()
        mock_subprocess.assert_not_called()
        # Todo: could get more specific about looking for the emitted failure signal

    def test_Device_export(self, mock_subprocess):
        filepath = "some/file/path"
        passphrase = "passphrase"

        with mock.patch(
            "securedrop_client.gui.conversation.export.device.TemporaryDirectory",
            return_value=self.mock_tmpdir,
        ):
            self.device.export([filepath], passphrase)

        expected_metadata = self.device._DISK_METADATA.copy()
        expected_metadata[self.device._DISK_ENCRYPTION_KEY_NAME] = passphrase

        self.device._create_archive.assert_called_once_with(
            archive_dir=_MOCK_FILEDIR,
            archive_fn=self.device._DISK_FN,
            metadata=expected_metadata,
            filepaths=[filepath],
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
        archive_path = None
        with TemporaryDirectory() as temp_dir:
            # We'll do this in the tmpdir for ease of cleanup
            open(os.path.join(temp_dir, "temp_1"), "w+").close()
            open(os.path.join(temp_dir, "temp_2"), "w+").close()
            filepaths = [os.path.join(temp_dir, "temp_1"), os.path.join(temp_dir, "temp_2")]
            device = Device()

            archive_path = device._create_archive(temp_dir, "mock.sd-export", {}, filepaths)

            assert archive_path == os.path.join(temp_dir, "mock.sd-export")
            assert os.path.exists(archive_path)  # sanity check

        assert not os.path.exists(archive_path)

    def test__create_archive_with_an_export_file(self, mocker):
        device = Device()
        archive_path = None
        with TemporaryDirectory() as temp_dir, NamedTemporaryFile() as export_file:
            archive_path = device._create_archive(
                temp_dir, "mock.sd-export", {}, [export_file.name]
            )
            assert archive_path == os.path.join(temp_dir, "mock.sd-export")
            assert os.path.exists(archive_path)  # sanity check

        assert not os.path.exists(archive_path)

    def test__create_archive_with_multiple_export_files(self, mocker):
        device = Device()
        archive_path = None
        with TemporaryDirectory() as tmpdir, NamedTemporaryFile() as f1, NamedTemporaryFile() as f2:
            transcript_path = os.path.join(tmpdir, "transcript.txt")
            with open(transcript_path, "a+") as transcript:
                archive_path = device._create_archive(
                    tmpdir,
                    "mock.sd-export",
                    {},
                    [f1.name, f2.name, transcript.name],
                )
                assert archive_path == os.path.join(tmpdir, "mock.sd-export")
                assert os.path.exists(archive_path)  # sanity check

        assert not os.path.exists(archive_path)

    def test__tmpdir_cleaned_up_on_exception(self, mock_sp):
        """
        Sanity check. If we encounter an error after archive has been built,
        ensure the tmpdir directory cleanup happens.
        """
        with TemporaryDirectory() as tmpdir, pytest.raises(ExportError):
            print(f"{tmpdir} created")

            raise ExportError("Something bad happened!")

        assert not os.path.exists(tmpdir)
