"""
A passphrase input that allows to show and hide it.

Copyright (C) 2018  The Freedom of the Press Foundation.

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published
by the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
"""
from PyQt5.QtWidgets import QDialog, QLineEdit

from securedrop_client.resources import load_icon


class PasswordEdit(QLineEdit):
    """
    A LineEdit with icons to show/hide password entries
    """

    def __init__(self, parent: QDialog) -> None:
        self.parent = parent
        super().__init__(self.parent)

        self.visibleIcon = load_icon("eye_visible.svg")
        self.hiddenIcon = load_icon("eye_hidden.svg")

        self.setEchoMode(QLineEdit.Password)
        self.togglepasswordAction = self.addAction(self.hiddenIcon, QLineEdit.TrailingPosition)
        self.togglepasswordAction.triggered.connect(self.on_toggle_password_Action)
        self.password_shown = False

    def on_toggle_password_Action(self) -> None:
        if not self.password_shown:
            self.setEchoMode(QLineEdit.Normal)
            self.password_shown = True
            self.togglepasswordAction.setIcon(self.visibleIcon)
        else:
            self.setEchoMode(QLineEdit.Password)
            self.password_shown = False
            self.togglepasswordAction.setIcon(self.hiddenIcon)
