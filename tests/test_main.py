import pytest
from unittest import mock
import os

#from securedrop_export.main import __main__, _exit_gracefully  # noqa: F401
from securedrop_export.main import Status, _extract_and_run, _exit_gracefully, _write_status  # noqa: F401
from securedrop_export.archive import Archive
# This import ensures at least the imports in main.__main__
# are executed during a test run

TEST_CONFIG = os.path.join(os.path.dirname(__file__), "sd-export-config.json")
BAD_TEST_CONFIG = os.path.join(os.path.dirname(__file__), "sd-export-config-bad.json")
ANOTHER_BAD_TEST_CONFIG = os.path.join(os.path.dirname(__file__), "sd-export-config-bad-2.json")


class TestMain():

    def test_exit_gracefully_no_exception(self, capsys):
        submission = Archive("testfile", TEST_CONFIG)
        
        with pytest.raises(SystemExit) as sysexit:
            _exit_gracefully(submission, Status.ERROR_GENERIC)

        # A graceful exit means a return code of 0
        assert sysexit.value.code == 0

        captured = capsys.readouterr()
        assert captured.err == "{}\n".format(Status.ERROR_GENERIC.value)
        assert captured.out == ""


    def test_exit_gracefully_exception(self, capsys):
        submission = Archive("testfile", TEST_CONFIG)

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

    @pytest.mark.parametrize("invalid_status", ["foo", ";ls", "&& echo 0"])
    def test_write_status_error(self, invalid_status, capsys):

        with pytest.raises(ValueError):
            _write_status(Status(invalid_status))


    def test__extract_and_run(self):
        pass


    def test__extract_and_run_failure(self):
        pass
