from PyQt5.QtWidgets import QApplication, QLineEdit

from securedrop_client.gui.base import PasswordEdit

app = QApplication([])


def test_PasswordEdit(mocker):
    passwordline = PasswordEdit(None)
    passwordline.togglepasswordAction.trigger()

    assert passwordline.echoMode() == QLineEdit.Normal
    passwordline.togglepasswordAction.trigger()
    assert passwordline.echoMode() == QLineEdit.Password
