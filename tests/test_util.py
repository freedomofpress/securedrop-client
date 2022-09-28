import pytest

from securedrop_export import utils
from securedrop_export.enums import ExportEnum
from securedrop_export.exceptions import ExportException

class FakeStatus(ExportEnum):
    OH_NO = "Oh No!"
    NO_PROBLEM = "No Problem!"

class TestUtil:

    def test_safe_check_call(self):
        # This works, since `ls` is a valid comand
        utils.safe_check_call(["ls"], FakeStatus.NO_PROBLEM)

    def test_safe_check_call_invalid_call(self):
        with pytest.raises(ExportException) as ex:
            utils.safe_check_call(["ls", "kjdsfhkdjfh"], FakeStatus.OH_NO)

        assert ex.value.sdstatus is FakeStatus.OH_NO

    def test_safe_check_call_write_to_stderr_and_ignore_error(self):
        utils.safe_check_call(
            ["python3", "-c", "import sys;sys.stderr.write('hello')"],
            FakeStatus.NO_PROBLEM,
            ignore_stderr_startswith=b"hello",
        )

    def test_safe_check_call_write_to_stderr_wrong_ignore_param(self):
        # This one writes to stderr and ignores the wrong string, so we expect an exception
        with pytest.raises(ExportException) as ex:
            utils.safe_check_call(
                ["python3", "-c", "import sys;sys.stderr.write('hello\n')"],
                FakeStatus.OH_NO,
                ignore_stderr_startswith=b"world",
            )

        assert ex.value.sdstatus is FakeStatus.OH_NO