import pytest
import os

from pathlib import Path
from securedrop_export import directory_util
from securedrop_export.exceptions import ExportException

class TestUtil:

    _TMPDIR_PATH = "/tmp/pretendium/"
    _REL_TRAVERSAL = "../../../whee"
    _SAFE_RELPATH = "./hi"
    _SAFE_RELPATH2 = "yay/a/path"
    _UNSAFE_RELPATH = "lgtm/../ohwait"

    def setup_method(self, method):
        pass

    def teadown_method(self, method):
        if (os.path.exists(self._TMPDIR_PATH)):
            os.remove(self._TMPDIR_PATH)

    def test_safe_mkdir_error_base_relpath(self):
        with pytest.raises(ValueError):
            directory_util.safe_mkdir(base_path=Path("."))

    def test_safe_mkdir_error_basepath_path_traversal(self):
        with pytest.raises(ValueError):
            directory_util.safe_mkdir(f"{self._TMPDIR_PATH}{self._REL_TRAVERSAL}")

    def test_safe_mkdir_error_relpath_path_traversal(self):
        with pytest.raises(ValueError):
            directory_util.safe_mkdir(f"{self._TMPDIR_PATH}", f"{self._REL_TRAVERSAL}")

    def test_safe_mkdir_success(self):
        directory_util.safe_mkdir(f"{self._TMPDIR_PATH}")

    def test_safe_mkdir_success_with_relpath(self):
        directory_util.safe_mkdir(f"{self._TMPDIR_PATH}", f"{self._SAFE_RELPATH}")

        assert (os.path.exists(f"{self._TMPDIR_PATH}{self._SAFE_RELPATH}"))

    def test_safe_mkdir_success_another_relpath(self):
        directory_util.safe_mkdir(f"{self._TMPDIR_PATH}", f"{self._SAFE_RELPATH2}")

        assert (os.path.exists(f"{self._TMPDIR_PATH}{self._SAFE_RELPATH2}"))
    
    def test_safe_mkdir_weird_path(self):
        with pytest.raises(ValueError):
            directory_util.safe_mkdir(f"{self._TMPDIR_PATH}", f"{self._UNSAFE_RELPATH}")

    def test__check_all_permissions_path_missing(self):
        with pytest.raises(ValueError):
            directory_util._check_all_permissions(f"{self._TMPDIR_PATH}", f"{self._SAFE_RELPATH}")

    def test_check_dir_perms_unsafe(self):
        path = Path(f"{self._TMPDIR_PATH}{self._SAFE_RELPATH}")

        directory_util.safe_mkdir(path)

        # Not what we want, ever
        path.chmod(0o666)
        
        with pytest.raises(RuntimeError):
           directory_util._check_dir_permissions(path)
