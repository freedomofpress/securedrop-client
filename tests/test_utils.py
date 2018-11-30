import pytest
from securedrop_client.utils import safe_mkdir, humanize_filesize


def test_safe_makedirs_non_absolute(homedir):
    with pytest.raises(ValueError) as e_info:
        safe_mkdir(homedir, '..')

    assert 'not absolute' in str(e_info.value)


def test_humanize_file_size_bytes():
    expected_humanized_filesize = "123 bytes"
    actual_humanized_filesize = humanize_filesize(123)
    assert expected_humanized_filesize == actual_humanized_filesize


def test_humanize_file_size_kilobytes():
    expected_humanized_filesize = "123KB"
    actual_humanized_filesize = humanize_filesize(123 * 1024)
    assert expected_humanized_filesize == actual_humanized_filesize


def test_humanize_file_size_megabytes():
    expected_humanized_filesize = "123MB"
    actual_humanized_filesize = humanize_filesize(123 * 1024 * 1024)
    assert expected_humanized_filesize == actual_humanized_filesize
