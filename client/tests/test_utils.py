import os
import tempfile
from pathlib import Path

import pytest

from securedrop_client.utils import (
    check_all_permissions,
    check_dir_permissions,
    check_path_traversal,
    humanize_filesize,
    relative_filepath,
    safe_mkdir,
)


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


def test_safe_mkdir_with_unsafe_path(homedir):
    """
    Ensure an error is raised if the path contains path traversal string.
    """
    with pytest.raises(ValueError) as e_info:
        safe_mkdir(homedir, "..")

    assert "Unsafe file or directory name: '..'" in str(e_info.value)


def test_safe_mkdir_with_base_dir_that_is_not_absolute():
    """
    Ensure an error is raised if the base dir is not an absolute path.
    """
    with pytest.raises(ValueError) as e_info:
        safe_mkdir("this/is/a/relative/path", "test")

    assert "Base directory 'this/is/a/relative/path' must be an absolute path" in str(e_info.value)


def test_safe_mkdir_with_first_param_containing_path_traversal_attack():
    """
    Test that safe_mkdir rejects a filename that could be used in a path traversal attack.
    """
    with pytest.raises(ValueError) as e:
        safe_mkdir("../../../../../../traversed")
    assert str(e.value) == "Base directory '../../../../../../traversed' must be an absolute path"


def test_safe_mkdir_with_second_param_containing_path_traversal_attack():
    """
    Test that safe_mkdir rejects a filename that could be used in a path traversal attack.
    """
    with tempfile.TemporaryDirectory() as temp_dir:
        with pytest.raises(ValueError) as e:
            safe_mkdir(temp_dir, "../../../../../../traversed")
        assert str(e.value) == "Unsafe file or directory name: '../../../../../../traversed'"


def test_safe_mkdir_with_second_param_containing_path_traversal_attack_with_preexisting_dirs():
    """
    Test that safe_mkdir rejects a filename that could be used in a path traversal attack
    when the home directory already exists.
    """
    with tempfile.TemporaryDirectory() as should_not_traverse_here:
        homedir = os.path.join(should_not_traverse_here, "homedir")
        os.mkdir(homedir)

        with pytest.raises(ValueError) as e:
            safe_mkdir(homedir, "../traversed")
        assert str(e.value) == "Unsafe file or directory name: '../traversed'"


def test_safe_mkdir_with_base_dir_with_parent_dirs_that_do_not_exist():
    """
    Ensure an error is raised if the parent directories of base dir do not exist.
    """
    with pytest.raises(FileNotFoundError) as e_info:
        safe_mkdir("/this/does/not/exist", "test")

    assert e_info.type == FileNotFoundError
    assert "No such file or directory: '/this/does/not/exist'" in str(e_info.value)


def test_safe_mkdir_with_base_dir_that_does_not_exist():
    """
    Ensure you can create a base dir if parent directories already exist.
    """
    with tempfile.TemporaryDirectory() as temp_dir:
        safe_mkdir(temp_dir)
        safe_mkdir(f"{temp_dir}/does-not-exist", "test")


def test_safe_mkdir_happy_path_with_secure_permissions():
    """
    Test that safe_mkdir works with one param.
    """
    with tempfile.TemporaryDirectory() as temp_dir:
        safe_mkdir(temp_dir)
        safe_mkdir(temp_dir, "test")
        assert oct(os.stat(temp_dir).st_mode) == "0o40700"
        assert oct(os.stat(os.path.join(temp_dir, "test")).st_mode) == "0o40700"

    with tempfile.TemporaryDirectory() as temp_dir:
        safe_mkdir(temp_dir, "test")
        assert oct(os.stat(temp_dir).st_mode) == "0o40700"
        assert oct(os.stat(os.path.join(temp_dir, "test")).st_mode) == "0o40700"


def test_safe_mkdir_sets_secure_permissions_for_each_directory_in_rel_path():
    """
    Test safe directory permissions when two paths are supplied.
    """
    with tempfile.TemporaryDirectory() as temp_dir:
        safe_mkdir(temp_dir, "check/each/dir/in/path")
        full_path = os.path.join(temp_dir, "check/each/dir/in/path")
        assert os.path.exists(full_path)
        assert oct(os.stat(temp_dir).st_mode) == "0o40700"
        assert oct(os.stat(os.path.join(temp_dir, "check")).st_mode) == "0o40700"
        assert oct(os.stat(os.path.join(temp_dir, "check/each")).st_mode) == "0o40700"
        assert oct(os.stat(os.path.join(temp_dir, "check/each/dir")).st_mode) == "0o40700"


def test_safe_mkdir_fixes_insecure_permissions_on_base_dir(homedir):
    """
    Test that safe_mkdir fixes insecure permissions on base dir.
    """
    with tempfile.TemporaryDirectory() as temp_dir:
        insecure_base_path = os.path.join(temp_dir, "base_dir")
        os.mkdir(insecure_base_path, 0o777)

        safe_mkdir(insecure_base_path)

        assert oct(os.stat(insecure_base_path).st_mode) == "0o40700"


def test_safe_mkdir_leaves_parent_dir_permissions_alone_on_base_path(homedir):
    """
    Test that safe_mkdir leaves base_dir parent permissions alone.
    """
    with tempfile.TemporaryDirectory() as temp_dir:
        os.chmod(temp_dir, 0o777)  # noqa: S103

        base_path = os.path.join(temp_dir, "base_dir")
        safe_mkdir(base_path)

        assert oct(os.stat(temp_dir).st_mode) == "0o40777"


def test_safe_mkdir_fixes_insecure_permissions_on_rel_dir(homedir):
    """
    Test that safe_mkdir raises when a parent directory has insecure permissions.
    """
    with tempfile.TemporaryDirectory() as temp_dir:
        os.mkdir(os.path.join(temp_dir, "rel"), 0o777)

        safe_mkdir(temp_dir, "rel")

        fixed_dir = Path(temp_dir).joinpath("rel")
        assert oct(os.stat(fixed_dir).st_mode) == "0o40700"


def test_safe_mkdir_fixes_insecure_permissions_on_parent_dir(homedir):
    """
    Test that safe_mkdir raises when a parent directory has insecure permissions.
    """
    with tempfile.TemporaryDirectory() as temp_dir:
        os.mkdir(os.path.join(temp_dir, "rel"), 0o700)
        os.mkdir(os.path.join(temp_dir, "rel/path"), 0o700)
        os.mkdir(os.path.join(temp_dir, "rel/path/test"), 0o777)

        safe_mkdir(temp_dir, "rel/path/test")

        fixed_dir = Path(temp_dir).joinpath("rel/path/test")
        assert oct(os.stat(fixed_dir).st_mode) == "0o40700"


def test_safe_mkdir_fixes_insecure_permissions_on_inner_parent_dir(homedir):
    """
    Test that safe_mkdir raises when a parent directory has insecure permissions.
    """
    with tempfile.TemporaryDirectory() as temp_dir:
        os.mkdir(os.path.join(temp_dir, "rel"), 0o700)
        os.mkdir(os.path.join(temp_dir, "rel/path"), 0o777)
        os.mkdir(os.path.join(temp_dir, "rel/path/test"), 0o700)

        safe_mkdir(temp_dir, "rel/path/test")

        fixed_dir = Path(temp_dir).joinpath("rel/path")
        assert oct(os.stat(fixed_dir).st_mode) == "0o40700"


def test_safe_mkdir_fixes_insecure_permissions_on_last_parent_dir(homedir):
    """
    Test that safe_mkdir raises when a parent directory has insecure permissions.
    """
    with tempfile.TemporaryDirectory() as temp_dir:
        os.mkdir(os.path.join(temp_dir, "rel"), 0o777)
        os.mkdir(os.path.join(temp_dir, "rel/path"), 0o700)
        os.mkdir(os.path.join(temp_dir, "rel/path/test"), 0o700)

        safe_mkdir(temp_dir, "rel/path/test")

        fixed_dir = Path(temp_dir).joinpath("rel")
        assert oct(os.stat(fixed_dir).st_mode) == "0o40700"


@pytest.mark.parametrize(
    ("args", "expected"),
    [
        (("/good/path", "/good"), "path"),
        (("/good/path", "/good/path"), "."),
        (("/good", "/"), "good"),
        (("/", "/"), "."),
    ],
)
def test_relative_filepath(args, expected):
    p = relative_filepath(*args)
    assert str(p) == expected


@pytest.mark.parametrize(
    ("args", "expected"),
    [
        (
            ("", ""),
            f"'{os.getcwd()}' is not in the subpath of '' OR one path is"
            " relative and the other is absolute.",
        ),
        (
            ("/base_dir", "../base_dir/must/be/absolute"),
            "'/base_dir' is not in the subpath of '../base_dir/must/be/absolute' OR one path is"
            " relative and the other is absolute.",
        ),
        (
            ("/bad/path", "/basedir"),
            "'/bad/path' is not in the subpath of '/basedir' OR one path is"
            " relative and the other is absolute.",
        ),
    ],
)
def test_relative_filepath_error(args, expected):
    with pytest.raises(ValueError) as e:
        relative_filepath(*args)
    assert expected == str(e.value)


def test_check_path_traversal():
    check_path_traversal("/good/path")
    check_path_traversal("good/path")

    with pytest.raises(ValueError) as e:
        check_path_traversal("../traversed")
    assert "Unsafe file or directory name" in str(e.value)

    with pytest.raises(ValueError) as e:
        check_path_traversal("x/../../traversed")
    assert "Unsafe file or directory name" in str(e.value)

    with pytest.raises(ValueError) as e:
        check_path_traversal("/x/../../traversed")
    assert "Unsafe file or directory name" in str(e.value)

    # Ultimately this traversal is safe but check_path_traversal only returns
    # successfully if there are no traversal attempts. See check_path_traversal
    # to understand behavior and reasoning behind design decision.
    with pytest.raises(ValueError) as e:
        check_path_traversal("x/../traversed")
    assert "Unsafe file or directory name" in str(e.value)

    with pytest.raises(ValueError) as e:
        check_path_traversal("/x/../traversed")
    assert "Unsafe file or directory name" in str(e.value)


def test_check_all_permissions():
    check_all_permissions("/this/path/does/not/exist/so/just/return", "/this/path")

    with tempfile.TemporaryDirectory() as temp_dir:
        os.mkdir(os.path.join(temp_dir, "bad"), 0o777)
        os.mkdir(os.path.join(temp_dir, "not_good"), 0o755)
        os.mkdir(os.path.join(temp_dir, "not_good/good"), 0o700)
        os.mkdir(os.path.join(temp_dir, "good"), 0o700)

        check_all_permissions(os.path.join(temp_dir, "bad"), temp_dir)
        assert oct(os.stat(os.path.join(temp_dir, "bad")).st_mode) == "0o40700"

        check_all_permissions(os.path.join(temp_dir, "not_good"), temp_dir)
        assert oct(os.stat(os.path.join(temp_dir, "not_good")).st_mode) == "0o40700"

        check_all_permissions(os.path.join(temp_dir, "not_good/good"), temp_dir)
        assert oct(os.stat(os.path.join(temp_dir, "not_good")).st_mode) == "0o40700"

        check_all_permissions(os.path.join(temp_dir, "good"), temp_dir)


def test_check_dir_permissions_unsafe(mocker):
    check_all_permissions("/this/path/does/not/exist/so/just/return", "/this/path")

    with tempfile.TemporaryDirectory() as temp_dir:
        os.mkdir(os.path.join(temp_dir, "bad"))
        os.chmod(os.path.join(temp_dir, "bad"), 0o0777)  # noqa: S103

        with pytest.raises(RuntimeError):
            check_dir_permissions(os.path.join(temp_dir, "bad"))
