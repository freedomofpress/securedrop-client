import unittest

from securedrop_client import state


class TestDebugging(unittest.TestCase):
    def test_file_identifiers_are_distinguishable(self):
        id = state.FileId("some file ID")
        assert "downloaded" not in id.__repr__()

        id = state.DownloadedFileId("another file ID")
        assert "downloaded" in id.__repr__()
