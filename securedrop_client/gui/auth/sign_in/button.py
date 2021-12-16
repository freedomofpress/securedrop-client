"""
Contains the main widgets used by the client to display things in the UI.

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
from gettext import gettext as _

from PyQt5.QtCore import Qt
from PyQt5.QtGui import QColor, QCursor
from PyQt5.QtWidgets import QGraphicsDropShadowEffect, QPushButton


class SignInButton(QPushButton):
    """
    A button that logs the user into application when clicked.
    """

    def __init__(self) -> None:
        super().__init__()
        self.setText(_("SIGN IN"))

        # Set css id
        self.setObjectName("SignInButton")

        self.setFixedHeight(40)
        self.setFixedWidth(140)

        # Set cursor.
        self.setCursor(QCursor(Qt.PointingHandCursor))

        # Set drop shadow effect
        effect = QGraphicsDropShadowEffect(self)
        effect.setOffset(0, 1)
        effect.setBlurRadius(8)
        effect.setColor(QColor("#aa000000"))
        self.setGraphicsEffect(effect)
        self.update()
