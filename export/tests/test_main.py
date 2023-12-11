import pytest
import tempfile
import os
from unittest import mock
import shutil

from securedrop_export.archive import Archive, Metadata, Status as ArchiveStatus
from securedrop_export.status import BaseStatus
from securedrop_export.command import Command
from securedrop_export.exceptions import ExportException

from securedrop_export.main import (
    Status,
    entrypoint,
    _exit_gracefully,
    _write_status,
    _start_service,
    _configure_logging,
)

SUBMISSION_SAMPLE_ARCHIVE = "pretendfile.tar.gz"


class TestMain:
    def setup_method(self, method):
        # This can't be a class method, since we expect sysexit during this test suite,
        # which
        self.submission = Archive("pretendfile.tar.gz")
        assert os.path.exists(self.submission.tmpdir)

    def teardown_method(self, method):
        if os.path.exists(self.submission.tmpdir):
            shutil.rmtree(self.submission.tmpdir)
        self.submission = None

    def test_exit_gracefully_no_exception(self, capsys):
        with pytest.raises(SystemExit) as sysexit:
            _exit_gracefully(self.submission, Status.ERROR_GENERIC)

        assert self._did_exit_gracefully(sysexit, capsys, Status.ERROR_GENERIC)

    def test_exit_gracefully_exception(self, capsys):
        with pytest.raises(SystemExit) as sysexit:
            _exit_gracefully(self.submission, Status.ERROR_GENERIC)

        # A graceful exit means a return code of 0
        assert self._did_exit_gracefully(sysexit, capsys, Status.ERROR_GENERIC)

    @pytest.mark.parametrize("status", [s for s in Status])
    def test_write_status(self, status, capsys):
        _write_status(status)
        captured = capsys.readouterr()
        assert captured.err == status.value + "\n"

    @pytest.mark.parametrize("invalid_status", ["foo", ";ls", "&& echo 0", None])
    def test_write_status_error(self, invalid_status, capsys):
        with pytest.raises(ValueError):
            _write_status(Status(invalid_status))

    def _did_exit_gracefully(self, exit, capsys, status: BaseStatus) -> bool:
        """
        Helper. True if exited with 0, writing supplied status to stderr.
        """
        captured = capsys.readouterr()

        return (
            exit.value.code == 0
            and captured.err.rstrip().endswith(status.value)
            and captured.out == ""
        )

    @pytest.mark.parametrize("command", list(Command))
    @mock.patch("securedrop_export.main._configure_logging")
    @mock.patch("os.path.exists", return_value=True)
    def test_entrypoint_success_start_service(self, mock_log, mock_path, command):
        metadata = os.path.join(self.submission.tmpdir, Metadata.METADATA_FILE)

        with open(metadata, "w") as f:
            f.write(f'{{"device": "{command.value}", "encryption_method": "luks"}}')

        with mock.patch(
            "sys.argv", ["qvm-send-to-usb", SUBMISSION_SAMPLE_ARCHIVE]
        ), mock.patch(
            "securedrop_export.main._start_service"
        ) as mock_service, mock.patch(
            "securedrop_export.main.Archive.extract_tarball",
            return_value=self.submission,
        ), pytest.raises(
            SystemExit
        ):
            entrypoint()

        if command is not Command.START_VM:
            assert self.submission.command == command
            assert mock_service.call_args[0][0].archive == SUBMISSION_SAMPLE_ARCHIVE
            mock_service.assert_called_once_with(self.submission)

    def test_valid_printer_test_config(self, capsys):
        Archive("testfile")
        temp_folder = tempfile.mkdtemp()
        metadata = os.path.join(temp_folder, Metadata.METADATA_FILE)
        with open(metadata, "w") as f:
            f.write('{"device": "printer-test"}')

        config = Metadata(temp_folder).validate()

        assert config.encryption_key is None
        assert config.encryption_method is None

    @mock.patch(
        "securedrop_export.archive.safe_extractall",
        side_effect=ValueError("A tarball problem!"),
    )
    @mock.patch("securedrop_export.main.os.path.exists", return_value=True)
    @mock.patch("securedrop_export.main.shutil.rmtree")
    @mock.patch("securedrop_export.main._configure_logging")
    def test_entrypoint_failure_extraction(
        self, mock_log, mock_rm, mock_path, mock_extract, capsys
    ):
        with mock.patch(
            "sys.argv", ["qvm-send-to-usb", SUBMISSION_SAMPLE_ARCHIVE]
        ), pytest.raises(SystemExit) as sysexit:
            entrypoint()

        assert self._did_exit_gracefully(
            sysexit, capsys, ArchiveStatus.ERROR_EXTRACTION
        )

    @mock.patch(
        "securedrop_export.main._configure_logging",
        side_effect=ExportException(
            sdstatus=Status.ERROR_LOGGING,
            sderror="Zounds, an error setting up logging!",
        ),
    )
    def test_entrypoint_logging_fails(self, mock_mkdir, capsys):
        with pytest.raises(SystemExit) as sysexit:
            entrypoint()

        assert self._did_exit_gracefully(sysexit, capsys, Status.ERROR_LOGGING)

    @mock.patch(
        "securedrop_export.main._configure_logging",
        side_effect=RuntimeError("Zounds, an uncaught error!"),
    )
    def test_entrypoint_fails_unexpected(self, mock_mkdir, capsys):
        with pytest.raises(SystemExit) as sysexit:
            entrypoint()

        assert self._did_exit_gracefully(sysexit, capsys, Status.ERROR_GENERIC)

    @mock.patch("os.path.exists", return_value=False)
    def test_entrypoint_archive_path_fails(self, mock_path, capsys):
        with pytest.raises(SystemExit) as sysexit:
            entrypoint()

        assert self._did_exit_gracefully(sysexit, capsys, Status.ERROR_FILE_NOT_FOUND)

    @mock.patch(
        "securedrop_export.main.safe_mkdir",
        side_effect=ValueError(1, "No logs for you!"),
    )
    def test__configure_logging_error(self, mock_mkdir, capsys):
        with pytest.raises(ExportException) as ex:
            _configure_logging()

        assert ex.value.sdstatus is Status.ERROR_LOGGING

    @pytest.mark.parametrize("command", list(Command))
    def test__start_service_calls_correct_services(self, command):
        if command is Command.START_VM:
            pytest.skip("Command does not start a service")

        self.submission.command = command

        with mock.patch("securedrop_export.main.PrintService") as ps, mock.patch(
            "securedrop_export.main.ExportService"
        ) as es:
            _start_service(self.submission)

        if command in [Command.PRINT, Command.PRINTER_TEST, Command.PRINTER_PREFLIGHT]:
            assert ps.call_args[0][0] is self.submission
        else:
            assert es.call_args[0][0] is self.submission
