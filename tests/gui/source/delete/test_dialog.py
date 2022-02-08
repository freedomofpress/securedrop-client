import unittest
from gettext import gettext as _

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

    @unittest.skip("WIP")
    def test_body_text(self):
        source = factory.Source()
        file = factory.File(source=source)
        message = factory.Message(source=source)
        message = factory.Message(source=source)
        reply = factory.Reply(source=source)


        expected_message = "".join(
            (
                "<style>",
                "p {{white-space: nowrap;}}",
                "</style>",
                "<p><b>",
                _("When the entire account for a source is deleted:"),
                "</b></p>",
                "<p><b>\u2219</b>&nbsp;",
                _("The source will not be able to log in with their codename again."),
                "</p>",
                "<p><b>\u2219</b>&nbsp;",
                _("Your organization will not be able to send them replies."),
                "</p>",
                "<p><b>\u2219</b>&nbsp;",
                _("All files and messages from that source will also be destroyed."),
                "</p>",
                "<p>&nbsp;</p>",
            )
        ).format(source=source.journalist_designation)
        assert self.dialog.text() == expected_message
