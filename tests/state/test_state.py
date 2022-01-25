import unittest

from securedrop_client import state


class TestState(unittest.TestCase):
    def setUp(self):
        self.state = state.State()

    def test_selected_conversation_is_unset_by_default(self):
        assert self.state.selected_conversation is None

    def test_selected_conversation_can_be_updated(self):
        self.state.selected_conversation = "0"
        assert self.state.selected_conversation == "0"

        # File identifiers can be of any shape.
        self.state.selected_conversation = 1
        assert self.state.selected_conversation == 1

    def test_add_file_does_not_duplicate_information(self):
        self.state.add_file(5, 1)
        self.state.add_file(5, 7)
        assert len(self.state.conversation_files(5)) == 2
        self.state.add_file(5, 7)
        assert len(self.state.conversation_files(5)) == 2

    def test_conversation_files_is_empty_by_default(self):
        assert len(self.state.conversation_files(2)) == 0

    def test_conversation_files_returns_the_conversation_files(self):
        self.state.add_file(4, 1)
        self.state.add_file(4, 7)
        self.state.add_file(4, 3)
        assert len(self.state.conversation_files(4)) == 3

        self.state.add_file(4, 8)
        assert len(self.state.conversation_files(4)) == 4

    def test_records_downloads(self):
        some_file_id = state.FileId("X")
        another_file_id = state.FileId("Y")
        self.state.add_file("4", some_file_id)
        self.state.add_file("4", another_file_id)
        files = self.state.conversation_files("4")
        assert len(files) == 2
        assert not files[0].is_downloaded
        assert not files[1].is_downloaded

        self.state.record_file_download(some_file_id)
        assert len(files) == 2
        assert files[0].is_downloaded
        assert not files[1].is_downloaded

    def test_record_downloads_ignores_missing_files(self):
        missing_file_id = state.FileId("missing")
        self.state.record_file_download(missing_file_id)
        assert True
