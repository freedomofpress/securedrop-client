import pytest
from unittest import mock
import shutil

from pathlib import Path
from securedrop_export.archive import Archive, Metadata, Status as ArchiveStatus
from securedrop_export.status import BaseStatus
from securedrop_export.command import Command
from securedrop_export.exceptions import ExportException
from securedrop_export.disk.status import Status as ExportStatus

from securedrop_export.main import (
    Status,
    entrypoint,
    _exit_gracefully,
    _write_status,
    _start_service,
    _configure_logging,
)

_PRINT_SAMPLE_ARCHIVE = "sample_print.sd_export"
_EXPORT_SAMPLE_ARCHIVE = "sample_export.sd_export"


class TestMain:
    def setup_method(self, method):
        # These can't be class setup methods, since we expect sysexit during this test suite
        self.print_archive_path = Path.cwd() / "tests/files" / _PRINT_SAMPLE_ARCHIVE
        assert self.print_archive_path.exists()

        self.export_archive_path = Path.cwd() / "tests/files" / _EXPORT_SAMPLE_ARCHIVE
        assert self.export_archive_path.exists()

        self.print_submission = Archive(str(self.print_archive_path))
        assert Path(self.print_submission.tmpdir).exists()

        self.export_submission = Archive(str(self.export_archive_path))
        assert Path(self.export_submission.tmpdir).exists()

    def teardown_method(self, method):
        if Path(self.print_submission.tmpdir).exists():
            shutil.rmtree(self.print_submission.tmpdir)

        if Path(self.export_submission.tmpdir).exists():
            shutil.rmtree(self.export_submission.tmpdir)

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

    def test__exit_gracefully_no_exception(self, capsys):
        with pytest.raises(SystemExit) as sysexit:
            # `ERROR_GENERIC` is just a placeholder status here
            _exit_gracefully(self.print_submission, Status.ERROR_GENERIC)

        assert self._did_exit_gracefully(sysexit, capsys, Status.ERROR_GENERIC)

    @mock.patch(
        "securedrop_export.main.shutil.rmtree",
        side_effect=FileNotFoundError("oh no", 0),
    )
    def test__exit_gracefully_even_with_cleanup_exception(self, mock_rm, capsys):
        with mock.patch(
            "sys.argv", ["qvm-send-to-usb", self.export_archive_path]
        ), mock.patch(
            "securedrop_export.main._start_service",
            return_value=ExportStatus.SUCCESS_EXPORT,
        ), pytest.raises(
            SystemExit
        ) as sysexit:
            entrypoint()

        assert self._did_exit_gracefully(sysexit, capsys, Status.ERROR_GENERIC)

    def test_entrypoint_success(self, capsys):
        with mock.patch(
            "sys.argv", ["qvm-send-to-usb", self.export_archive_path]
        ), mock.patch(
            "securedrop_export.main._start_service",
            return_value=ExportStatus.SUCCESS_EXPORT,
        ), pytest.raises(
            SystemExit
        ) as sysexit:
            entrypoint()

        assert self._did_exit_gracefully(sysexit, capsys, ExportStatus.SUCCESS_EXPORT)

    @pytest.mark.parametrize("status", [s for s in Status])
    def test__write_status_success(self, status, capsys):
        _write_status(status)
        captured = capsys.readouterr()
        assert captured.err == status.value + "\n"

    @pytest.mark.parametrize("invalid_status", ["foo", ";ls", "&& echo 0", None])
    def test__write_status_will_not_write_bad_value(self, invalid_status, capsys):
        with pytest.raises(ValueError):
            _write_status(Status(invalid_status))

        captured = capsys.readouterr()
        assert captured.err == ""
        assert captured.out == ""

    def test_entrypoint_success_start_service(self):
        with mock.patch(
            "sys.argv", ["qvm-send-to-usb", self.export_archive_path]
        ), mock.patch(
            "securedrop_export.main._start_service"
        ) as mock_service, pytest.raises(
            SystemExit
        ):
            entrypoint()

        assert mock_service.call_args[0][0].archive == self.export_archive_path
        assert mock_service.call_args[0][0].command == Command.EXPORT

    def test_validate_metadata(self):
        for archive_path in [self.print_archive_path, self.export_archive_path]:
            archive = Archive(archive_path)
            extracted = archive.extract_tarball()

            assert Metadata(extracted.tmpdir).validate()

    @mock.patch(
        "securedrop_export.archive.safe_extractall",
        side_effect=ValueError("A tarball problem!"),
    )
    def test_entrypoint_failure_extraction(self, mock_extract, capsys):
        with mock.patch(
            "sys.argv", ["qvm-send-to-usb", self.export_archive_path]
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

    def test_entrypoint_archive_path_fails(self, capsys):
        with mock.patch(
            "sys.argv", ["qvm-send-to-usb", "THIS_FILE_DOES_NOT_EXIST.sd_export"]
        ), pytest.raises(SystemExit) as sysexit:
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

        mock_submission = Archive("mock_submission.sd_export")
        mock_submission.command = command

        with mock.patch("securedrop_export.main.PrintService") as ps, mock.patch(
            "securedrop_export.main.ExportService"
        ) as es:
            _start_service(mock_submission)

        if command in [Command.PRINT, Command.PRINTER_TEST, Command.PRINTER_PREFLIGHT]:
            assert ps.call_args[0][0] is mock_submission
        else:
            assert es.call_args[0][0] is mock_submission
