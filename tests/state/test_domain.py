import unittest

from securedrop_client import state as local


class TestFile(unittest.TestCase):
    def test_files_can_be_downloaded(self):
        file = local.File("some opaque identifier")
        assert file.id == local.FileId("some opaque identifier")
        assert not file.is_downloaded

        file.is_downloaded = True
        assert file.is_downloaded
