import os
import pytest
import tempfile

from securedrop_client.utils import humanize_filesize, safe_mkdir


def test_safe_makedirs_non_absolute(homedir):
    with pytest.raises(ValueError) as e_info:
        safe_mkdir(homedir, "..")

    assert "not absolute" in str(e_info.value)


def test_humanize_file_size_bytes():
    expected_humanized_filesize = "123B"
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


def test_safe_mkdir_with_first_param_containing_path_traversal_attack():
    """
    Test that safe_mkdir rejects a filename that could be used in a path traversal attack.
    """
    with pytest.raises(ValueError) as e:
        safe_mkdir("../../../../../../traversed")
        assert f"traversed is not an absolute path" in str(e.value)


def test_safe_mkdir_with_second_param_containing_path_traversal_attack():
    """
    Test that safe_mkdir rejects a filename that could be used in a path traversal attack.
    """
    with tempfile.TemporaryDirectory() as temp_dir:
        with pytest.raises(ValueError) as e:
            safe_mkdir(temp_dir, "../../../../../../traversed")
            assert f"'/traversed' does not start with '{temp_dir}'" in str(e.value)


def test_safe_mkdir_with_second_param_containing_path_traversal_attack_with_preexisting_dirs():
    """
    Test that safe_mkdir rejects a filename that could be used in a path traversal attack
    when the home directory already exists.
    """
    with tempfile.TemporaryDirectory() as should_not_traverse_here:
        homedir = os.path.join(should_not_traverse_here, 'homedir')
        os.mkdir(homedir)

        with pytest.raises(ValueError) as e:
            safe_mkdir(homedir, "../traversed")
            assert f"'{should_not_traverse_here}/traversed' does not start with '{homedir}'" in str(
                e.value
            )
