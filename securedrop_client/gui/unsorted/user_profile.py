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
from __future__ import annotations

import logging
from gettext import gettext as _

from PyQt5.QtCore import QSize, Qt, pyqtSlot
from PyQt5.QtGui import QBrush, QCursor, QFont, QPalette
from PyQt5.QtWidgets import QHBoxLayout, QLabel, QSizePolicy

from securedrop_client.db import User
from securedrop_client.gui.unsorted.login_button import LoginButton
from securedrop_client.gui.unsorted.user_button import UserButton
from securedrop_client.gui.unsorted.user_icon_label import UserIconLabel
from securedrop_client.logic import Controller

logger = logging.getLogger(__name__)


class UserProfile(QLabel):
    """
    A widget that contains user profile information and options.

    Displays user profile icon, name, and menu options if the user is logged in. Displays a login
    button if the user is logged out.
    """

    def __init__(self) -> None:
        super().__init__()

        # Set css id
        self.setObjectName("UserProfile")

        # Set background
        palette = QPalette()
        palette.setBrush(
            QPalette.Background, QBrush(Qt.NoBrush)
        )  # This makes the widget transparent
        self.setPalette(palette)
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)

        # Set layout
        layout = QHBoxLayout(self)
        self.setLayout(layout)

        # Remove margins
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Login button
        self.login_button = LoginButton()

        # User button
        self.user_button = UserButton()

        # User icon
        self.user_icon = UserIconLabel()
        self.user_icon.setObjectName("UserProfile_icon")  # Set css id
        self.user_icon.setFixedSize(QSize(30, 30))
        self.user_icon.setAlignment(Qt.AlignCenter)
        self.user_icon_font = QFont()
        self.user_icon_font.setLetterSpacing(QFont.AbsoluteSpacing, 0.58)
        self.user_icon.setFont(self.user_icon_font)
        self.user_icon.clicked.connect(self.user_button.click)
        self.user_icon.setCursor(QCursor(Qt.PointingHandCursor))

        # Add widgets to user auth layout
        layout.addWidget(self.login_button, alignment=Qt.AlignTop)
        layout.addWidget(self.user_icon, alignment=Qt.AlignTop)
        layout.addWidget(self.user_button, alignment=Qt.AlignTop)

    def setup(self, window, controller: Controller) -> None:  # type: ignore[no-untyped-def]
        self.controller = controller
        self.controller.update_authenticated_user.connect(self._on_update_authenticated_user)
        self.user_button.setup(controller)
        self.login_button.setup(window)

    @pyqtSlot(User)
    def _on_update_authenticated_user(self, db_user: User) -> None:
        self.set_user(db_user)

    def set_user(self, db_user: User) -> None:
        self.user_icon.setText(_(db_user.initials))
        self.user_button.set_username(_(db_user.fullname))

    def show(self) -> None:
        self.login_button.hide()
        self.user_icon.show()
        self.user_button.show()

    def hide(self) -> None:
        self.user_icon.hide()
        self.user_button.hide()
        self.login_button.show()
