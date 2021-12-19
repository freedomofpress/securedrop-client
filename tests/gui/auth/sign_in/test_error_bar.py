from PyQt5.QtWidgets import QApplication

from securedrop_client.gui.auth.sign_in import LoginErrorBar

app = QApplication([])


def test_LoginErrorBar_set_message(mocker):
    error_bar = LoginErrorBar()
    error_bar.error_status_bar = mocker.MagicMock()
    mocker.patch.object(error_bar, "show")

    error_bar.set_message("mock error")

    error_bar.error_status_bar.setText.assert_called_with("mock error")
    error_bar.show.assert_called_with()


def test_LoginErrorBar_clear_message(mocker):
    error_bar = LoginErrorBar()
    error_bar.error_status_bar = mocker.MagicMock()
    mocker.patch.object(error_bar, "hide")

    error_bar.clear_message()

    error_bar.error_status_bar.setText.assert_called_with("")
    error_bar.hide.assert_called_with()
