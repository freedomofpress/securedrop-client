import os
import shutil
import tarfile
import tempfile
from pathlib import Path

import pytest

from securedrop_export import directory


class TestDirectory:
    _REL_TRAVERSAL = "../../../whee"
    _SAFE_RELPATH = "./hi"
    _SAFE_RELPATH2 = "yay/a/path"
    _UNSAFE_RELPATH = "lgtm/../ohwait"

    @classmethod
    def setup_class(cls):
        cls.homedir = tempfile.mkdtemp() + "/"

    @classmethod
    def teardown_class(cls):
        if os.path.exists(cls.homedir):
            shutil.rmtree(cls.homedir)

    def setup_method(self, method):
        pass

    def teadown_method(self, method):
        if os.path.exists(self.homedir):
            os.remove(self.homedir)

    def test_safe_mkdir_error_base_relpath(self):
        with pytest.raises(ValueError):
            directory.safe_mkdir(base_path=Path("."))

    def test_safe_mkdir_error_basepath_path_traversal(self):
        with pytest.raises(ValueError):
            directory.safe_mkdir(f"{self.homedir}{self._REL_TRAVERSAL}")

    def test_safe_mkdir_error_relpath_path_traversal(self):
        with pytest.raises(ValueError):
            directory.safe_mkdir(f"{self.homedir}", f"{self._REL_TRAVERSAL}")

    def test_safe_mkdir_success(self):
        directory.safe_mkdir(f"{self.homedir}")

    def test_safe_mkdir_success_with_relpath(self):
        directory.safe_mkdir(f"{self.homedir}", f"{self._SAFE_RELPATH}")

        assert os.path.exists(f"{self.homedir}{self._SAFE_RELPATH}")

    def test_safe_mkdir_success_another_relpath(self):
        directory.safe_mkdir(f"{self.homedir}", f"{self._SAFE_RELPATH2}")

        assert os.path.exists(f"{self.homedir}{self._SAFE_RELPATH2}")

    def test_safe_mkdir_weird_path(self):
        with pytest.raises(ValueError):
            directory.safe_mkdir(f"{self.homedir}", f"{self._UNSAFE_RELPATH}")

    def test__check_all_permissions_path_missing(self):
        with pytest.raises(ValueError):
            directory._check_all_permissions(f"{self.homedir}", f"{self._SAFE_RELPATH}")

    def test_check_dir_perms_unsafe(self):
        path = Path(f"{self.homedir}{self._SAFE_RELPATH}")

        directory.safe_mkdir(path)

        # Not what we want, ever
        path.chmod(0o666)

        with pytest.raises(RuntimeError):
            directory._check_dir_permissions(path)

    def test_check_all_perms_invalid_full_path(self):
        path = Path(f"{self.homedir}/idontexist")
        base = Path(f"{self.homedir}")

        # Returns without error
        assert directory._check_all_permissions(path, base) is None

    def test_safe_extractall_implicitly_created_directories(self):
        """Test that implicitly created parent directories have 0o700 permissions."""
        # Create a temporary directory for the archive and extraction
        archive_dir = tempfile.mkdtemp()
        extract_dir = tempfile.mkdtemp()

        try:
            # Create a tar archive with nested files but without explicit directory entries
            archive_path = os.path.join(archive_dir, "test.tar")
            with tarfile.open(archive_path, "w") as tar:
                # Create a file in a nested directory structure
                file_path = os.path.join(archive_dir, "file.txt")
                with open(file_path, "w") as f:
                    f.write("test content")

                # Add the file with a nested path but don't add parent directories explicitly
                tar.add(file_path, arcname="level1/level2/level3/file.txt")

            # Extract using safe_extractall
            directory.safe_extractall(archive_path, extract_dir)

            # Verify all implicitly created directories have 0o700 permissions
            level1_path = os.path.join(extract_dir, "level1")
            level2_path = os.path.join(extract_dir, "level1/level2")
            level3_path = os.path.join(extract_dir, "level1/level2/level3")

            for dir_path in [level1_path, level2_path, level3_path]:
                stat_res = os.stat(dir_path).st_mode
                masked = stat_res & 0o777
                assert masked == 0o700, (
                    f"Directory {dir_path} has permissions {oct(masked)}, expected 0o700"
                )

        finally:
            shutil.rmtree(archive_dir)
            shutil.rmtree(extract_dir)

    def test_safe_extractall_multiple_nested_paths(self):
        """Test that all implicitly created directories have correct perms with multiple paths."""
        # Create a temporary directory for the archive and extraction
        archive_dir = tempfile.mkdtemp()
        extract_dir = tempfile.mkdtemp()

        try:
            # Create a tar archive with multiple nested files
            archive_path = os.path.join(archive_dir, "test.tar")
            with tarfile.open(archive_path, "w") as tar:
                # Create multiple files with different nested paths
                for i, nested_path in enumerate(
                    [
                        "dir1/subdir1/file1.txt",
                        "dir1/subdir2/file2.txt",
                        "dir2/subdir1/subsubdir/file3.txt",
                    ]
                ):
                    file_path = os.path.join(archive_dir, f"file{i}.txt")
                    with open(file_path, "w") as f:
                        f.write(f"test content {i}")
                    tar.add(file_path, arcname=nested_path)

            # Extract using safe_extractall
            directory.safe_extractall(archive_path, extract_dir)

            # Verify all directories have 0o700 permissions
            dirs_to_check = [
                "dir1",
                "dir1/subdir1",
                "dir1/subdir2",
                "dir2",
                "dir2/subdir1",
                "dir2/subdir1/subsubdir",
            ]

            for rel_dir in dirs_to_check:
                dir_path = os.path.join(extract_dir, rel_dir)
                stat_res = os.stat(dir_path).st_mode
                masked = stat_res & 0o777
                assert masked == 0o700, (
                    f"Directory {dir_path} has permissions {oct(masked)}, expected 0o700"
                )

        finally:
            shutil.rmtree(archive_dir)
            shutil.rmtree(extract_dir)

    def test_safe_extractall_explicit_and_implicit_directories(self):
        """Test permissions when archive contains both explicit and implicit directory entries."""
        # Create a temporary directory for the archive and extraction
        archive_dir = tempfile.mkdtemp()
        extract_dir = tempfile.mkdtemp()

        try:
            # Create a tar archive with both explicit directories and files in nested paths
            archive_path = os.path.join(archive_dir, "test.tar")
            with tarfile.open(archive_path, "w") as tar:
                # Add an explicit directory entry with wrong permissions
                explicit_dir = os.path.join(archive_dir, "explicit_dir")
                os.makedirs(explicit_dir, mode=0o755)  # Wrong permissions
                tar.add(explicit_dir, arcname="explicit_dir")

                # Add a file in a nested path under the explicit directory
                file_path = os.path.join(archive_dir, "file.txt")
                with open(file_path, "w") as f:
                    f.write("test content")
                tar.add(file_path, arcname="explicit_dir/implicit_subdir/file.txt")

            # Extract using safe_extractall
            directory.safe_extractall(archive_path, extract_dir)

            # Verify all directories have 0o700 permissions (including the explicit one)
            explicit_dir_path = os.path.join(extract_dir, "explicit_dir")
            implicit_subdir_path = os.path.join(extract_dir, "explicit_dir/implicit_subdir")

            for dir_path in [explicit_dir_path, implicit_subdir_path]:
                stat_res = os.stat(dir_path).st_mode
                masked = stat_res & 0o777
                assert masked == 0o700, (
                    f"Directory {dir_path} has permissions {oct(masked)}, expected 0o700"
                )

        finally:
            shutil.rmtree(archive_dir)
            shutil.rmtree(extract_dir)
