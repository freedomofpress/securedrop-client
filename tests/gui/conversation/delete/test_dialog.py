from PyQt5.QtWidgets import QApplication

from securedrop_client.gui.conversation import DeleteConversationDialog

app = QApplication([])


def test_DeleteConversationDialog_continue(mocker, source, session):
    source = source["source"]  # to get the Source object

    mock_controller = mocker.MagicMock()
    dialog = DeleteConversationDialog(source, mock_controller)
    dialog.continue_button.click()
    mock_controller.delete_conversation.assert_called_once_with(source)


def test_DeleteConversationDialog_exec(mocker, source, session):
    """
    Test that the dialog body is updated every time it is opened, to ensure
    that the file, message and reply counters are up-to-date.
    """
    source = source["source"]  # to get the Source object

    mock_controller = mocker.MagicMock()
    dialog = DeleteConversationDialog(source, mock_controller)
    mocker.patch.object(dialog.body, "setText")
    mocker.patch("securedrop_client.gui.widgets.ModalDialog.exec")
    dialog.exec()
    dialog.body.setText.assert_called_once()
