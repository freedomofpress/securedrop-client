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
from PyQt5.QtWidgets import QLineEdit, QWidget


class PasswordEdit(QLineEdit):
    """
    A LineEdit with icons to show/hide password entries
    """

    def __init__(self, parent: QWidget) -> None:
        super().__init__(parent)

        self.setEchoMode(QLineEdit.Password)
        self.password_shown = False

    def on_toggle_password_Action(self) -> None:
        if not self.password_shown:
            self.setEchoMode(QLineEdit.Normal)
            self.password_shown = True
        else:
            self.setEchoMode(QLineEdit.Password)
            self.password_shown = False
