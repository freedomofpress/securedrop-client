import unittest

from PyQt5.QtTest import QSignalSpy

from securedrop_client.gui import conversation
from tests.helper import app  # noqa: F401


class TestErrorDialog(unittest.TestCase):
    @unittest.skip("TODO: the dialog text should include its header's text")
    def test_displays_which_file_was_not_printed(self):
        file_name = "little_bird/conversation.txt"
        reason = "printer unavailable"
        dialog = conversation.PrintErrorDialog(file_name, reason)
        self.assertTrue(file_name in dialog.text())

    def test_displays_why_the_file_was_not_printed(self):
        file_name = "little_bird/conversation.txt"
        reason = "printer unavailable"
        dialog = conversation.PrintErrorDialog(file_name, reason)
        self.assertTrue(reason in dialog.text())

    def test_emits_finished_signal_when_accepted(self):
        file_name = "little_bird/conversation.txt"
        reason = "printer unavailable"
        dialog = conversation.PrintErrorDialog(file_name, reason)
        dialog_finished_emissions = QSignalSpy(dialog.finished)
        self.assertTrue(dialog_finished_emissions.isValid())

        dialog.accept()
        self.assertEqual(len(dialog_finished_emissions), 1)
