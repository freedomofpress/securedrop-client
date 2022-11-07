import unittest
from unittest import mock
from unittest.mock import MagicMock

from PyQt5.QtCore import QTimer
from PyQt5.QtWidgets import QDialog, QMenu

from securedrop_client import state
from securedrop_client.db import Source
from securedrop_client.gui.actions import (
    DeleteConversationAction,
    DeleteSourceAction,
    DownloadConversation,
)
from securedrop_client.logic import Controller
from tests import factory
from tests.helper import app  # noqa: F401


class DeleteConversationActionTest(unittest.TestCase):
    def setUp(self):
        self._source = factory.Source()
        _menu = QMenu()
        self._controller = MagicMock(Controller, api=True)
        self._app_state = MagicMock(
            state.State, selected_conversation=state.ConversationId("some_conversation")
        )
        self._dialog = QDialog()

        def _dialog_constructor(source: Source) -> QDialog:
            return self._dialog

        self.action = DeleteConversationAction(
            self._source, _menu, self._controller, _dialog_constructor, self._app_state
        )

    def test_deletes_conversation_when_dialog_accepted(self):
        # Accept the confirmation dialog from a separate thread.
        QTimer.singleShot(10, self._dialog.accept)

        self.action.trigger()

        self._controller.delete_conversation.assert_called_once_with(self._source)
        self._app_state.remove_conversation_files.assert_called_once_with(
            state.ConversationId("some_conversation")
        )

    def test_does_not_delete_conversation_when_dialog_rejected(self):
        # Reject the confirmation dialog from a separate thread.
        QTimer.singleShot(10, self._dialog.reject)

        self.action.trigger()

        assert not self._controller.delete_conversation.called
        assert not self._app_state.remove_conversation_files.called

    def test_requires_authenticated_journalist(self):
        controller = mock.MagicMock(Controller, api=None)  # no authenticated user
        self.action.controller = controller

        confirmation_dialog = mock.MagicMock()
        self.action._confirmation_dialog = confirmation_dialog

        self.action.trigger()

        assert not confirmation_dialog.exec.called
        assert not controller.delete_conversation.called
        controller.on_action_requiring_login.assert_called_once()

    def test_deletes_nothing_if_no_conversation_is_selected(self):
        self._app_state.selected_conversation = None

        # Accept the confirmation dialog from a separate thread.
        QTimer.singleShot(10, self._dialog.accept)

        self.action.trigger()

        assert not self._controller.delete_conversation.called
        assert not self._app_state.remove_conversation_files.called


class DeleteSourceActionTest(unittest.TestCase):
    def setUp(self):
        self._source = factory.Source()
        _menu = QMenu()
        self._controller = MagicMock(Controller, api=True)
        self._dialog = QDialog()

        def _dialog_constructor(source: Source) -> QDialog:
            return self._dialog

        self.action = DeleteSourceAction(self._source, _menu, self._controller, _dialog_constructor)

    def test_deletes_source_when_dialog_accepted(self):
        # Accept the confirmation dialog from a separate thread.
        QTimer.singleShot(10, self._dialog.accept)

        self.action.trigger()

        self._controller.delete_source.assert_called_once_with(self._source)

    def test_does_not_delete_source_when_dialog_rejected(self):
        # Reject the confirmation dialog from a separate thread.
        QTimer.singleShot(10, self._dialog.reject)

        self.action.trigger()

        assert not self._controller.delete_source.called

    def test_requires_authenticated_journalist(self):
        controller = mock.MagicMock(Controller, api=None)  # no authenticated user
        self.action.controller = controller

        confirmation_dialog = mock.MagicMock()
        self.action._confirmation_dialog = confirmation_dialog

        self.action.trigger()

        assert not confirmation_dialog.exec.called
        assert not controller.delete_source.called
        controller.on_action_requiring_login.assert_called_once()


class TestDownloadConversation(unittest.TestCase):
    def test_trigger(self):
        menu = QMenu()
        controller = MagicMock(Controller, api=True)
        app_state = state.State()
        action = DownloadConversation(menu, controller, app_state)

        conversation_id = state.ConversationId("some_conversation")
        app_state.selected_conversation = conversation_id

        action.trigger()

        controller.download_conversation.assert_called_once_with(conversation_id)

    def test_requires_authenticated_journalist(self):
        menu = QMenu()
        controller = mock.MagicMock(Controller, api=None)  # no authenticated user
        app_state = state.State()
        action = DownloadConversation(menu, controller, app_state)

        conversation_id = state.ConversationId("some_conversation")
        app_state.selected_conversation = conversation_id

        action.trigger()

        assert not controller.download_conversation.called
        controller.on_action_requiring_login.assert_called_once()

    def test_trigger_downloads_nothing_if_no_conversation_is_selected(self):
        menu = QMenu()
        controller = MagicMock(Controller, api=True)
        app_state = state.State()
        action = DownloadConversation(menu, controller, app_state)

        action.trigger()
        assert controller.download_conversation.not_called

    def test_gets_disabled_when_no_files_to_download_remain(self):
        menu = QMenu()
        controller = MagicMock(Controller, api=True)
        app_state = state.State()
        action = DownloadConversation(menu, controller, app_state)

        conversation_id = state.ConversationId(3)
        app_state.selected_conversation = conversation_id

        app_state.add_file(conversation_id, 5)
        app_state.file(5).is_downloaded = True

        action.setEnabled(True)  # only for extra contrast
        app_state.selected_conversation_files_changed.emit()
        assert not action.isEnabled()

    def test_gets_enabled_when_files_are_available_to_download(self):
        menu = QMenu()
        controller = MagicMock(Controller, api=True)
        app_state = state.State()
        action = DownloadConversation(menu, controller, app_state)

        conversation_id = state.ConversationId(3)
        app_state.selected_conversation = conversation_id

        app_state.add_file(conversation_id, 5)
        app_state.file(5).is_downloaded = False

        action.setEnabled(False)  # only for extra contrast
        app_state.selected_conversation_files_changed.emit()
        assert action.isEnabled()

    def test_gets_initially_disabled_when_file_information_is_available(self):
        menu = QMenu()
        controller = MagicMock(Controller, api=True)
        app_state = state.State()

        conversation_id = state.ConversationId(3)
        app_state.selected_conversation = conversation_id
        app_state.add_file(conversation_id, 5)
        app_state.file(5).is_downloaded = True

        action = DownloadConversation(menu, controller, app_state)

        assert not action.isEnabled()

    def test_gets_initially_enabled_when_file_information_is_available(self):
        menu = QMenu()
        controller = MagicMock(Controller, api=True)
        app_state = state.State()

        conversation_id = state.ConversationId(3)
        app_state.selected_conversation = conversation_id
        app_state.add_file(conversation_id, 5)
        app_state.file(5).is_downloaded = False

        action = DownloadConversation(menu, controller, app_state)

        assert action.isEnabled()

    def test_does_not_require_state_to_be_defined(self):
        menu = QMenu()
        controller = MagicMock(Controller, api=True)
        action = DownloadConversation(menu, controller, app_state=None)

        action.setEnabled(False)
        assert not action.isEnabled()

        action.setEnabled(True)
        assert action.isEnabled()

    def test_on_selected_conversation_files_changed_handles_missing_state_gracefully(
        self,
    ):
        menu = QMenu()
        controller = MagicMock(Controller, api=True)
        action = DownloadConversation(menu, controller, None)

        action.setEnabled(True)
        action._on_selected_conversation_files_changed()
        assert action.isEnabled()

        action.setEnabled(False)
        action._on_selected_conversation_files_changed()
        assert not action.isEnabled()
