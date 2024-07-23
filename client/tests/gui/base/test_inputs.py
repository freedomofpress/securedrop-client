from PyQt5.QtWidgets import QCheckBox, QLineEdit

from securedrop_client.gui.base import PasswordEdit


def test_PasswordEdit(mocker):
    checkbox = QCheckBox()
    passwordline = PasswordEdit(None)

    passwordline.on_toggle_password_Action()
    checkbox.isChecked()
    assert passwordline.echoMode() == QLineEdit.Normal
    passwordline.on_toggle_password_Action()
    assert passwordline.echoMode() == QLineEdit.Password
