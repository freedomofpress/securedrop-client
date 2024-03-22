import unittest

from PyQt5.QtCore import QTimer

from securedrop_client.gui.conversation.delete import DeleteConversationDialog as Dialog
from tests import factory


class DeleteConversationDialogTest(unittest.TestCase):
    def setUp(self):
        self._source = factory.Source()
        factory.File(source=self._source)
        self.dialog = Dialog(self._source)

    def test_displays_accurate_source_information_by_default(self):
        assert "one file" in self.dialog.text()
        assert "0 messages" in self.dialog.text()
        assert "0 replies" in self.dialog.text()

    def test_displays_updated_source_information_when_shown(self):
        for i in range(2):
            factory.Reply(source=self._source)
        for i in range(3):
            factory.Message(source=self._source)

        QTimer.singleShot(300, self.dialog.close)
        self.dialog.exec()

        assert "3 messages" in self.dialog.text()
        assert "2 replies" in self.dialog.text()
        assert "one file" in self.dialog.text()

    def test_default_button_performs_action(self):
        # This test does rely on an implementation detail (the buttons)
        # but I couldn't find a way to test this properly using key events.
        assert self.dialog.continue_button.isDefault()
        assert not self.dialog.cancel_button.isDefault()
