import pytest
from unittest import mock
import os

from securedrop_export.main import Status, entrypoint, _extract_and_run, _exit_gracefully, _write_status  # noqa: F401
from securedrop_export.archive import Archive

class TestMain():

    def test_exit_gracefully_no_exception(self, capsys):
        submission = Archive("testfile")
        
        with pytest.raises(SystemExit) as sysexit:
            _exit_gracefully(submission, Status.ERROR_GENERIC)

        # A graceful exit means a return code of 0
        assert sysexit.value.code == 0

        captured = capsys.readouterr()
        assert captured.err == "{}\n".format(Status.ERROR_GENERIC.value)
        assert captured.out == ""


    def test_exit_gracefully_exception(self, capsys):
        submission = Archive("testfile")

        with pytest.raises(SystemExit) as sysexit:
            exception = mock.MagicMock()
            exception.output = "BANG!"
            _exit_gracefully(submission, Status.ERROR_GENERIC, e=exception)

        # A graceful exit means a return code of 0
        assert sysexit.value.code == 0

        captured = capsys.readouterr()
        assert captured.err.rstrip() == Status.ERROR_GENERIC.value
        assert captured.out == ""


    @pytest.mark.parametrize("status", [s for s in Status])
    def test_write_status(self, status, capsys):
        _write_status(status)
        captured = capsys.readouterr()
        assert captured.err == status.value + "\n"

    @pytest.mark.parametrize("invalid_status", ["foo", ";ls", "&& echo 0", None])
    def test_write_status_error(self, invalid_status, capsys):

        with pytest.raises(ValueError):
            _write_status(Status(invalid_status))


    def test__extract_and_run(self):
        pass


    def test__extract_and_run_failure(self):
        pass

    def test_entrypoint(self):
        pass
