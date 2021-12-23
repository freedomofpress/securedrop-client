from PyQt5.QtWidgets import QApplication

from securedrop_client.gui.conversation import SourceMenu
from securedrop_client.gui.source import DeleteSourceDialog

app = QApplication([])


def test_DeleteSource_from_source_menu_when_user_is_loggedout(mocker):
    mock_controller = mocker.MagicMock()
    mock_controller.api = None
    mock_source = mocker.MagicMock()
    mock_delete_source_dialog_instance = mocker.MagicMock(DeleteSourceDialog)
    mock_delete_source_dialog = mocker.MagicMock()
    mock_delete_source_dialog.return_value = mock_delete_source_dialog_instance

    mocker.patch("securedrop_client.gui.source.DeleteSourceDialog", mock_delete_source_dialog)
    source_menu = SourceMenu(mock_source, mock_controller)
    source_menu.actions()[2].trigger()
    mock_delete_source_dialog_instance.exec.assert_not_called()
