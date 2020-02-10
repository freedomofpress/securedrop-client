from PyQt5.QtCore import Qt


from securedrop_client.gui.main import Window
from securedrop_client.gui.widgets import LoginDialog


def test_login(qtbot, mocker):
    """
    We see an error if incomplete credentials are supplied to the login dialog.
    """
    w = Window()
    login_dialog = LoginDialog(w)
    login_dialog.error_bar.set_message = mocker.MagicMock()
    login_dialog.show()
    qtbot.addWidget(login_dialog)
    assert login_dialog.error_bar.error_status_bar.text() == ""
    qtbot.keyClicks(login_dialog.username_field, "journalist")
    qtbot.mouseClick(login_dialog.submit, Qt.LeftButton)
    assert login_dialog.error_bar.set_message.call_count == 1
    assert login_dialog.error_bar.isVisible()
