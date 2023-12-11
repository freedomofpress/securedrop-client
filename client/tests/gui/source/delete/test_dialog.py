import unittest

from securedrop_client.gui.source.delete import DeleteSourceDialog as Dialog
from tests import factory
from tests.helper import app  # noqa: F401


class DeleteSourceDialogTest(unittest.TestCase):
    def setUp(self):
        self._source = factory.Source()
        factory.File(source=self._source)
        self.dialog = Dialog(self._source)

    def test_default_button_is_safer_choice(self):
        # This test does rely on an implementation detail (the buttons)
        # but I couldn't find a way to test this properly using key events.
        assert not self.dialog.continue_button.isDefault()
        assert self.dialog.cancel_button.isDefault()

    def test_displays_important_information_when_shown(self):
        assert "not be able to send them replies" in self.dialog.text()
        assert "source will not be able to log in" in self.dialog.text()
        assert "files and messages from that source will also be destroyed" in self.dialog.text()
