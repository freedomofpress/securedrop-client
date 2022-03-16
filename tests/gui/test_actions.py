import unittest
from unittest import mock

from PyQt5.QtWidgets import QApplication, QMenu

from securedrop_client import state
from securedrop_client.gui.actions import (
    DeleteConversationAction,
    DeleteSourceAction,
    DownloadConversation,
)
from securedrop_client.gui.conversation import DeleteConversationDialog
from securedrop_client.gui.source import DeleteSourceDialog

app = QApplication([])


def test_DeleteSourceAction_init(mocker):
    mock_controller = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    DeleteSourceAction(mock_source, None, mock_controller)


def test_DeleteSourceAction_trigger(mocker):
    mock_controller = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    mock_delete_source_dialog_instance = mocker.MagicMock(DeleteSourceDialog)
    mock_delete_source_dialog = mocker.MagicMock()
    mock_delete_source_dialog.return_value = mock_delete_source_dialog_instance

    mocker.patch("securedrop_client.gui.actions.DeleteSourceDialog", mock_delete_source_dialog)
    delete_source_action = DeleteSourceAction(mock_source, None, mock_controller)
    delete_source_action.trigger()
    mock_delete_source_dialog_instance.exec.assert_called_once()


def test_DeleteConversationAction_trigger(mocker):
    mock_controller = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    mock_delete_conversation_dialog_instance = mocker.MagicMock(DeleteConversationDialog)
    mock_delete_conversation_dialog = mocker.MagicMock()
    mock_delete_conversation_dialog.return_value = mock_delete_conversation_dialog_instance

    mocker.patch(
        "securedrop_client.gui.actions.DeleteConversationDialog", mock_delete_conversation_dialog
    )
    delete_conversation_action = DeleteConversationAction(mock_source, None, mock_controller)
    delete_conversation_action.trigger()
    mock_delete_conversation_dialog_instance.exec.assert_called_once()


def test_DeleteConversationAction_trigger_when_user_is_loggedout(mocker):
    mock_controller = mocker.MagicMock()
    mock_controller.api = None
    mock_source = mocker.MagicMock()
    mock_delete_conversation_dialog_instance = mocker.MagicMock(DeleteConversationDialog)
    mock_delete_conversation_dialog = mocker.MagicMock()
    mock_delete_conversation_dialog.return_value = mock_delete_conversation_dialog_instance

    mocker.patch(
        "securedrop_client.gui.conversation.DeleteConversationDialog",
        mock_delete_conversation_dialog,
    )
    delete_conversation_action = DeleteConversationAction(mock_source, None, mock_controller)
    delete_conversation_action.trigger()
    mock_delete_conversation_dialog_instance.exec.assert_not_called()


def test_DeleteSourceAction_requires_an_authenticated_journalist(mocker):
    mock_controller = mocker.MagicMock()
    mock_controller.api = None  # no aouthenticated journalist
    mock_source = mocker.MagicMock()
    mock_delete_source_dialog_instance = mocker.MagicMock(DeleteSourceDialog)
    mock_delete_source_dialog = mocker.MagicMock()
    mock_delete_source_dialog.return_value = mock_delete_source_dialog_instance

    mocker.patch("securedrop_client.gui.actions.DeleteSourceDialog", mock_delete_source_dialog)
    delete_source_action = DeleteSourceAction(mock_source, None, mock_controller)
    delete_source_action.trigger()
    assert not mock_delete_source_dialog_instance.exec.called
    mock_controller.on_action_requiring_login.assert_called_once()


class TestDownloadConversation(unittest.TestCase):
    def test_trigger(self):
        menu = QMenu()
        controller = mock.MagicMock()
        app_state = state.State()
        action = DownloadConversation(menu, controller, app_state)

        conversation_id = state.ConversationId("some_conversation")
        app_state.selected_conversation = conversation_id

        action.trigger()

        controller.download_conversation.assert_called_once_with(conversation_id)

    def test_trigger_downloads_nothing_if_no_conversation_is_selected(self):
        menu = QMenu()
        controller = mock.MagicMock()
        app_state = state.State()
        action = DownloadConversation(menu, controller, app_state)

        action.trigger()
        assert controller.download_conversation.not_called

    def test_gets_disabled_when_no_files_to_download_remain(self):
        menu = QMenu()
        controller = mock.MagicMock()
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
        controller = mock.MagicMock()
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
        controller = mock.MagicMock()
        app_state = state.State()

        conversation_id = state.ConversationId(3)
        app_state.selected_conversation = conversation_id
        app_state.add_file(conversation_id, 5)
        app_state.file(5).is_downloaded = True

        action = DownloadConversation(menu, controller, app_state)

        assert not action.isEnabled()

    def test_gets_initially_enabled_when_file_information_is_available(self):
        menu = QMenu()
        controller = mock.MagicMock()
        app_state = state.State()

        conversation_id = state.ConversationId(3)
        app_state.selected_conversation = conversation_id
        app_state.add_file(conversation_id, 5)
        app_state.file(5).is_downloaded = False

        action = DownloadConversation(menu, controller, app_state)

        assert action.isEnabled()

    def test_does_not_require_state_to_be_defined(self):
        menu = QMenu()
        controller = mock.MagicMock()
        action = DownloadConversation(menu, controller, app_state=None)

        action.setEnabled(False)
        assert not action.isEnabled()

        action.setEnabled(True)
        assert action.isEnabled()

    def test_on_selected_conversation_files_changed_handles_missing_state_gracefully(
        self,
    ):
        menu = QMenu()
        controller = mock.MagicMock()
        action = DownloadConversation(menu, controller, None)

        action.setEnabled(True)
        action._on_selected_conversation_files_changed()
        assert action.isEnabled()

        action.setEnabled(False)
        action._on_selected_conversation_files_changed()
        assert not action.isEnabled()
