import os
import shutil
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
