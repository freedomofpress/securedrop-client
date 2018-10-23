import os
import pytest


@pytest.fixture(scope='function')
def safe_tmpdir(tmpdir):
    os.chmod(str(tmpdir), 0o0700)
    return tmpdir
