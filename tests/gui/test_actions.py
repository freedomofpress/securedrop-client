import unittest
from unittest.mock import MagicMock

from PyQt5.QtCore import QTimer
from PyQt5.QtWidgets import QApplication, QDialog, QMenu

from securedrop_client.db import Source
from securedrop_client.gui.actions import DeleteConversationAction
from securedrop_client.logic import Controller
from tests import factory

app = QApplication([])


class DeleteConversationActionTest(unittest.TestCase):
    def setUp(self):
        self._source = factory.Source()
        _menu = QMenu()
        self._controller = MagicMock(Controller, api=True)
        self._dialog = QDialog()

        def _dialog_constructor(source: Source) -> QDialog:
            return self._dialog

        self.action = DeleteConversationAction(
            self._source, _menu, self._controller, _dialog_constructor
        )

    def test_deletes_conversation_when_dialog_accepted(self):
        # Accept the confimation dialog from a separate thread.
        timer = QTimer()
        timer.start(10)
        timer.timeout.connect(lambda: self._dialog.accept())

        self.action.trigger()

        self._controller.delete_conversation.assert_called_once_with(self._source)

    def test_does_not_delete_conversation_when_dialog_rejected(self):
        # Reject the confimation dialog from a separate thread.
        timer = QTimer()
        timer.start(10)
        timer.timeout.connect(lambda: self._dialog.reject())

        self.action.trigger()

        assert not self._controller.delete_conversation.called
