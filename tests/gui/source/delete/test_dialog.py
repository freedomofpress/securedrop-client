import unittest

from PyQt5.QtWidgets import QApplication

from securedrop_client.gui.source.delete import Dialog
from tests import factory

app = QApplication([])


class SourceDeleteDialogTest(unittest.TestCase):
    def setUp(self):
        self._source = factory.Source()
        factory.File(source=self._source)
        self.dialog = Dialog(self._source)

    def test_default_button_is_safer_choice(self):
        # This test does rely on an implementation detail (the buttons)
        # but I couldn't find a way to test this properly using key events.
        assert not self.dialog.continue_button.isDefault()
        assert self.dialog.cancel_button.isDefault()
