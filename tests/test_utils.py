import pytest
from securedrop_client.utils import safe_mkdir


def test_safe_makedirs_non_absolute(safe_tmpdir):
    home_dir = str(safe_tmpdir)

    with pytest.raises(ValueError) as e_info:
        safe_mkdir(home_dir, '..')

    assert 'not absolute' in str(e_info.value)
