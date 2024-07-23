import unittest
from collections import namedtuple
from unittest import mock

from PyQt5.QtTest import QSignalSpy

from securedrop_client import state
from tests.helper import app  # noqa: F401

Source = namedtuple("Source", ["uuid"])
File = namedtuple("File", ["uuid", "source", "is_downloaded"])


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

    def test_selected_conversation_can_be_set_from_an_optional_source_id_and_cleared(self):
        source_id = state.SourceId("some_id")
        self.state.set_selected_conversation_for_source(source_id)
        assert self.state.selected_conversation == state.ConversationId("some_id")

        self.state.clear_selected_conversation()
        assert self.state.selected_conversation is None

    def test_add_file_does_not_duplicate_information(self):
        self.state.add_file(5, 1)
        self.state.add_file(5, 7)
        assert len(self.state.conversation_files(5)) == 2
        self.state.add_file(5, 7)
        assert len(self.state.conversation_files(5)) == 2

    def test_remove_conversation_files_removes_all_conversation_files(self):
        self.state.add_file(7, 3)
        self.state.add_file(7, 1)
        assert len(self.state.conversation_files(7)) == 2
        self.state.remove_conversation_files(7)
        assert len(self.state.conversation_files(7)) == 0

    def test_remove_conversation_files_handles_missing_files_gracefully(self):
        self.state.remove_conversation_files(8)
        assert len(self.state.conversation_files(8)) == 0

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

    def test_selected_conversation_files_changed_signal_is_emited_when_meaningful(self):
        signal_emissions = QSignalSpy(self.state.selected_conversation_files_changed)

        # when the selected conversation changed
        self.state.selected_conversation = 1
        assert len(signal_emissions) == 1

        # NOT when a file is added to a conversation that's not the selected one
        self.state.add_file("some_conversation_id", "file_id")
        assert len(signal_emissions) == 1  # the signal wasn't emitted again

        # when a known file was downloaded
        self.state.record_file_download("file_id")
        assert len(signal_emissions) == 2

        # when a file is added to the selected conversation
        self.state.add_file(1, "some_file_id")
        assert len(signal_emissions) == 3

        # NOT when files are removed from a conversation that's not the selected one
        self.state.remove_conversation_files("some_conversation_id")
        assert len(signal_emissions) == 3  # the signal wasn't emitted again

        # when the selected conversation files are removed
        self.state.remove_conversation_files(1)
        assert len(signal_emissions) == 4

    def test_selected_conversation_has_downloadable_files_false_by_default(self):
        assert not self.state.selected_conversation_has_downloadable_files

    def test_selected_conversation_has_downloadable_files_false_when_all_files_are_downloaded(self):
        self.state.selected_conversation = 1
        self.state.add_file(1, "some_file_id")
        self.state.add_file(1, "another_file_id")

        self.state.add_file("conversation that's not selected", "unrelated_file")
        self.state.file("unrelated_file").is_downloaded = False  # to be explicit

        self.state.file("some_file_id").is_downloaded = True
        self.state.file("another_file_id").is_downloaded = True
        assert not self.state.selected_conversation_has_downloadable_files

        self.state.file("some_file_id").is_downloaded = False
        assert self.state.selected_conversation_has_downloadable_files

    def test_gets_initialized_when_created_with_a_database(self):
        source = Source(uuid="id")
        file_1 = File(uuid="one", source=source, is_downloaded=True)
        file_2 = File(uuid="two", source=source, is_downloaded=False)

        database = mock.MagicMock()
        database.get_files = mock.MagicMock(return_value=[file_1, file_2])

        initialized_state = state.State(database)
        assert initialized_state.file(state.FileId("one")).is_downloaded
        assert not initialized_state.file(state.FileId("two")).is_downloaded

        assert len(initialized_state.conversation_files(state.ConversationId("id"))) == 2
