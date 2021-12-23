from PyQt5.QtWidgets import QApplication

from securedrop_client.gui.actions import DeleteConversationAction, DeleteSourceAction
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
    mock_delete_conversation_dialog_instance = mocker.MagicMock(DeleteSourceDialog)
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
    mock_delete_conversation_dialog_instance = mocker.MagicMock(DeleteSourceDialog)
    mock_delete_conversation_dialog = mocker.MagicMock()
    mock_delete_conversation_dialog.return_value = mock_delete_conversation_dialog_instance

    mocker.patch(
        "securedrop_client.gui.conversation.DeleteConversationDialog",
        mock_delete_conversation_dialog,
    )
    delete_conversation_action = DeleteConversationAction(mock_source, None, mock_controller)
    delete_conversation_action.trigger()
    mock_delete_conversation_dialog_instance.exec.assert_not_called()
