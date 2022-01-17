import unittest

from securedrop_client import state


class TestState(unittest.TestCase):
    def setUp(self):
        self.state = state.State()

    def test_selected_conversation_is_unset_by_default(self):
        assert self.state.selected_conversation() is None

    def test_selected_conversation_can_be_updated(self):
        self.state.set_selected_conversation(0)
        assert self.state.selected_conversation() == "0"

        self.state.set_selected_conversation(1)
        assert self.state.selected_conversation() == "1"

    def test_conversation_files_is_empty_by_default(self):
        assert len(self.state.conversation_files(2)) == 0

    def test_conversation_files_returns_the_conversation_files(self):
        self.state.update_or_insert_conversation(4, [1, 7, 3])
        print(self.state)
        assert len(self.state.conversation_files(4)) == 3

        self.state.update_or_insert_conversation(4, [1, 7, 3, 8])
        assert len(self.state.conversation_files(4)) == 4

        self.state.update_or_insert_conversation(4, [9])
        assert len(self.state.conversation_files(4)) == 1

    def test_displays_the_selected_conversation(self):
        self.state.update_or_insert_conversation(4, [1, 7, 3, 8])
        assert "selected_conversation: None" in str(self.state)

        self.state.set_selected_conversation(3)
        assert "selected_conversation: 3" in str(self.state)

    def test_displays_all_conversation_files(self):
        self.state.set_selected_conversation(7)
        assert "conversation_files: {}" in str(self.state)

        self.state.update_or_insert_conversation(4, [1, 7, 3, 8])
        assert "conversation_files: {4: [1, 7, 3, 8]}" in str(self.state)

    def test_records_downloads(self):
        some_file_id = state.FileId("X")
        another_file_id = state.FileId("Y")
        self.state.update_or_insert_conversation("4", [some_file_id, another_file_id])
        files = self.state.conversation_files("4")
        assert len(files) == 2
        assert isinstance(files[0], state.FileId)
        assert isinstance(files[1], state.FileId)

        self.state.record_file_download(some_file_id)
        assert len(files) == 2
        assert isinstance(files[0], state.DownloadedFileId)
        assert isinstance(files[1], state.FileId)
