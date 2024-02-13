import os
import tarfile
from tempfile import NamedTemporaryFile, TemporaryDirectory
from unittest import mock

import pytest
from PyQt5.QtTest import QSignalSpy

from securedrop_client.export import Export
from securedrop_client.export_status import ExportError, ExportStatus
from tests import factory

_PATH_TO_PRETEND_ARCHIVE = "/tmp/archive-pretend"
_QREXEC_EXPORT_COMMAND = (
    "/usr/bin/qrexec-client-vm",
    [
        "--",
        "sd-devices",
        "qubes.OpenInVM",
        "/usr/lib/qubes/qopen-in-vm",
        "--view-only",
        "--",
        f"{_PATH_TO_PRETEND_ARCHIVE}",
    ],
)
_MOCK_FILEDIR = "/tmp/mock_tmpdir/"

# A few different status values to be used in test paramaterization
_SAMPLE_EXPORT = [
    ExportStatus.NO_DEVICE_DETECTED,
    ExportStatus.DEVICE_WRITABLE,
    ExportStatus.ERROR_MOUNT,
    ExportStatus.ERROR_MISSING_FILES,
    ExportStatus.SUCCESS_EXPORT,
]
_SAMPLE_PRINT_PREFLIGHT_FAIL = [
    ExportStatus.ERROR_PRINTER_NOT_FOUND,
    ExportStatus.ERROR_PRINTER_DRIVER_UNAVAILABLE,
]


class TestDevice:
    @classmethod
    def setup_class(cls):
        cls.device = None

    # Reset any manually-changed mock values before next test
    @classmethod
    def setup_method(cls):
        cls.mock_file = factory.File(source=factory.Source())
        cls.mock_file_location = f"{_MOCK_FILEDIR}{cls.mock_file.filename}"
        cls.device = Export()
        cls.device._create_archive = mock.MagicMock()
        cls.device._create_archive.return_value = _PATH_TO_PRETEND_ARCHIVE
        cls.mock_tmpdir = mock.MagicMock()
        cls.mock_tmpdir.__enter__ = mock.MagicMock(return_value=_MOCK_FILEDIR)

    @classmethod
    def teardown_method(cls):
        cls.mock_file = None
        cls.device._create_archive = None

    def test_Device_run_printer_preflight_checks(self):
        with mock.patch(
            "securedrop_client.export.mkdtemp",
            return_value=self.mock_tmpdir,
        ), mock.patch("securedrop_client.export.QProcess") as mock_qprocess, mock.patch.object(
            self.device, "_create_archive"
        ) as mock_archive:
            mock_archive.return_value = _PATH_TO_PRETEND_ARCHIVE
            mock_qproc = mock_qprocess.return_value
            mock_qproc.start = mock.MagicMock()
            mock_qproc.readAllStandardError.return_value = (
                ExportStatus.PRINT_PREFLIGHT_SUCCESS.value.encode("utf-8")
            )
            self.device.run_printer_preflight_checks()

            mock_qproc.start.assert_called_once()
            assert (
                mock_qproc.start.call_args[0] == _QREXEC_EXPORT_COMMAND
            ), f"Actual: {mock_qproc.start.call_args[0]}"

    def test_Device_run_print_preflight_checks_with_error(self):
        spy = QSignalSpy(self.device.print_preflight_check_failed)
        with mock.patch(
            "securedrop_client.export.mkdtemp",
            return_value=self.mock_tmpdir,
        ), mock.patch("securedrop_client.export.QProcess") as mock_qprocess, mock.patch.object(
            self.device, "_create_archive"
        ) as mock_archive, mock.patch(
            "shutil.rmtree"
        ) as mock_rmtree:
            mock_archive.return_value = _PATH_TO_PRETEND_ARCHIVE
            mock_qproc = mock_qprocess.return_value
            mock_qproc.start = mock.MagicMock()
            mock_qproc.start.side_effect = (
                lambda proc, args: self.device._on_print_preflight_complete()
            )  # This ain't doin it
            mock_qproc.readAllStandardError.data.return_value = b"Not a real status\n"

            self.device.run_printer_preflight_checks()

            mock_qproc.start.assert_called_once()
            mock_rmtree.assert_called_once()

        # Note: in future can return UNEXPECTED_RETURN_STATUS instead
        assert (
            len(spy) == 1
            and isinstance(spy[0][0], ExportError)
            and spy[0][0].status == ExportStatus.ERROR_PRINT
        )

    def test_Device_print(self):
        with mock.patch("securedrop_client.export.QProcess") as mock_qprocess, mock.patch(
            "securedrop_client.export.mkdtemp",
            return_value=self.mock_tmpdir,
        ):
            mock_qproc = mock_qprocess.return_value
            mock_qproc.start = mock.MagicMock()

            self.device.print([self.mock_file_location])

            mock_qproc.start.assert_called_once()
            assert mock_qproc.start.call_args[0] == _QREXEC_EXPORT_COMMAND

            self.device._create_archive.assert_called_once_with(
                archive_dir=self.mock_tmpdir,
                archive_fn=self.device._PRINT_FN,
                metadata=self.device._PRINT_METADATA,
                filepaths=[self.mock_file_location],
            )

    @mock.patch("shutil.rmtree")
    def test_Device_print_file_file_missing(self, mock_shutil):
        device = Export()
        spy = QSignalSpy(device.print_failed)

        with mock.patch(
            "securedrop_client.export.mkdtemp",
            return_value=self.mock_tmpdir,
        ), mock.patch("securedrop_client.export.QProcess") as mock_qprocess:
            mock_qproc = mock_qprocess.return_value
            mock_qproc.start = mock.MagicMock()

            device.print("some-missing-file-uuid")

            mock_qproc.start.assert_not_called()

        # Print doesn't use the new ERROR_MISSING_FILES status yet
        assert (
            len(spy) == 1
            and isinstance(spy[0][0], ExportError)
            and spy[0][0].status == ExportStatus.ERROR_PRINT
        )

    def test_Device_run_export_preflight_checks(self):
        with mock.patch(
            "securedrop_client.export.mkdtemp",
            return_value=self.mock_tmpdir,
        ), mock.patch("securedrop_client.export.QProcess") as mock_qprocess:
            mock_qproc = mock_qprocess.return_value
            mock_qproc.start = mock.MagicMock()

            self.device.run_export_preflight_checks()

            mock_qproc.start.assert_called_once()
            assert mock_qproc.start.call_args[0] == _QREXEC_EXPORT_COMMAND

        self.device._create_archive.assert_called_once_with(
            archive_dir=self.mock_tmpdir,
            archive_fn=self.device._USB_TEST_FN,
            metadata=self.device._USB_TEST_METADATA,
        )

    @mock.patch("shutil.rmtree")
    def test_Device_run_export_preflight_checks_with_error(self, mock_shutil):
        spy = QSignalSpy(self.device.export_state_changed)

        with mock.patch(
            "securedrop_client.export.mkdtemp",
            return_value=self.mock_tmpdir,
        ), mock.patch.object(self.device, "_create_archive"), mock.patch(
            "securedrop_client.export.QProcess"
        ) as mock_qprocess, mock.patch.object(
            self.device, "_create_archive"
        ) as mock_archive:
            mock_archive.return_value = _PATH_TO_PRETEND_ARCHIVE
            mock_qproc = mock_qprocess.return_value
            mock_qproc.start = mock.MagicMock()
            mock_qproc.start.side_effect = (
                lambda proc, args: self.device._on_export_process_complete()
            )
            mock_qproc.readAllStandardError = mock.MagicMock()
            mock_qproc.readAllStandardError.data.return_value = b"Houston, we have a problem\n"

            self.device.run_export_preflight_checks()

            assert len(spy) == 1 and spy[0][0] == ExportStatus.UNEXPECTED_RETURN_STATUS

    def test_Device_export_file_missing(self, mocker):
        device = Export()

        warning_logger = mocker.patch("securedrop_client.export.logger.warning")
        with mock.patch(
            "securedrop_client.export.tarfile.open",
            return_value=mock.MagicMock(),
        ), mock.patch(
            "securedrop_client.export.mkdtemp",
            return_value=self.mock_tmpdir,
        ), mock.patch(
            "securedrop_client.export.QProcess"
        ) as mock_qprocess:
            device.export(["/not/a/real/location"], "mock passphrase")

            mock_qprocess.assert_not_called()

        warning_logger.assert_called_once()
        # Todo: could get more specific about looking for the emitted failure signal

    def test_Device_export(self):
        filepath = "some/file/path"
        passphrase = "passphrase"

        expected_metadata = self.device._DISK_METADATA.copy()
        expected_metadata[self.device._DISK_ENCRYPTION_KEY_NAME] = passphrase

        with mock.patch(
            "securedrop_client.export.mkdtemp",
            return_value=self.mock_tmpdir,
        ), mock.patch("securedrop_client.export.QProcess") as mock_qprocess:
            mock_qproc = mock_qprocess.return_value
            mock_qproc.start = mock.MagicMock()
            self.device.export([filepath], passphrase)

            mock_qproc.start.assert_called_once()
            assert mock_qproc.start.call_args[0] == _QREXEC_EXPORT_COMMAND

        self.device._create_archive.assert_called_once_with(
            archive_dir=self.mock_tmpdir,
            archive_fn=self.device._DISK_FN,
            metadata=expected_metadata,
            filepaths=[filepath],
        )

    @pytest.mark.parametrize("status", [i.value for i in _SAMPLE_EXPORT])
    def test__run_qrexec_sends_export_signal(self, status):
        spy = QSignalSpy(self.device.export_state_changed)
        enum = ExportStatus(status)
        with mock.patch("securedrop_client.export.QProcess") as mock_qprocess:
            mock_qproc = mock_qprocess.return_value
            mock_qproc.finished = mock.MagicMock()
            mock_qproc.start = mock.MagicMock()
            mock_qproc.start.side_effect = (
                lambda proc, args: self.device._on_export_process_complete()
            )
            mock_qproc.readAllStandardError.return_value.data.return_value = f"{status}\n".encode(
                "utf-8"
            )

            self.device._run_qrexec_export(
                _PATH_TO_PRETEND_ARCHIVE,
                self.device._on_export_process_complete,
                self.device._on_export_process_error,
            )

            mock_qproc.start.assert_called_once()
            assert len(spy) == 1 and spy[0][0] == enum

    @pytest.mark.parametrize("status", [i.value for i in _SAMPLE_PRINT_PREFLIGHT_FAIL])
    def test__run_qrexec_sends_print_failed_signal(self, status):
        spy = QSignalSpy(self.device.print_preflight_check_failed)
        enum = ExportStatus(status)
        with mock.patch("securedrop_client.export.QProcess") as mock_qprocess:
            mock_qproc = mock_qprocess.return_value
            mock_qproc.finished = mock.MagicMock()
            mock_qproc.start = mock.MagicMock()
            mock_qproc.start.side_effect = (
                lambda proc, args: self.device._on_print_preflight_complete()
            )
            mock_qproc.readAllStandardError.return_value.data.return_value = f"{status}\n".encode(
                "utf-8"
            )

            self.device._run_qrexec_export(
                _PATH_TO_PRETEND_ARCHIVE,
                self.device._on_print_preflight_complete,
                self.device._on_print_prefight_error,
            )

            mock_qproc.start.assert_called_once()
            assert len(spy) == 1 and isinstance(spy[0][0], ExportError) and spy[0][0].status == enum

    @mock.patch("securedrop_client.export.tarfile")
    def test__add_virtual_file_to_archive(self, mock_tarfile):
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
            device = Export()

            archive_path = device._create_archive(temp_dir, "mock.sd-export", {}, filepaths)

            assert archive_path == os.path.join(temp_dir, "mock.sd-export")
            assert os.path.exists(archive_path)  # sanity check

        assert not os.path.exists(archive_path)

    def test__create_archive_with_an_export_file(self):
        device = Export()
        archive_path = None
        with TemporaryDirectory() as temp_dir, NamedTemporaryFile() as export_file:
            archive_path = device._create_archive(
                temp_dir, "mock.sd-export", {}, [export_file.name]
            )
            assert archive_path == os.path.join(temp_dir, "mock.sd-export")
            assert os.path.exists(archive_path)  # sanity check

        assert not os.path.exists(archive_path)

    def test__create_archive_with_multiple_export_files(self):
        device = Export()
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

    def test__tmpdir_cleaned_up_on_exception(self):
        """
        Sanity check. If we encounter an error after archive has been built,
        ensure the tmpdir directory cleanup happens.
        """
        with mock.patch(
            "securedrop_client.export.mkdtemp", return_value=self.mock_tmpdir
        ), mock.patch("securedrop_client.export.QProcess") as qprocess, mock.patch.object(
            self.device, "_cleanup_tmpdir"
        ) as mock_cleanup:
            mock_qproc = qprocess.return_value
            mock_qproc.readAllStandardError.data.return_value = b"Something awful happened!\n"
            mock_qproc.start = lambda proc, args: self.device._on_export_process_error()
            self.device.run_printer_preflight_checks()
            assert self.device.tmpdir == self.mock_tmpdir
            mock_cleanup.assert_called_once()
