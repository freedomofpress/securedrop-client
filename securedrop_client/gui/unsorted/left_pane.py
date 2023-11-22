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

from PyQt5.QtWidgets import QLabel, QVBoxLayout, QWidget

from securedrop_client.db import User
from securedrop_client.gui.unsorted.user_profile import UserProfile
from securedrop_client.logic import Controller
from securedrop_client.resources import load_image

logger = logging.getLogger(__name__)


class LeftPane(QWidget):
    """
    Represents the left side pane that contains user authentication actions and information.
    """

    def __init__(self) -> None:
        super().__init__()

        self.setObjectName("LeftPane")

        # Set layout
        layout = QVBoxLayout(self)
        self.setLayout(layout)

        # Remove margins and spacing
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        self.branding_barre = QLabel()
        self.branding_barre.setPixmap(load_image("left_pane.svg"))
        self.user_profile = UserProfile()

        # Hide user profile widget until user logs in
        self.user_profile.hide()

        # Add widgets to layout
        layout.addWidget(self.user_profile)
        layout.addWidget(self.branding_barre)

    def setup(self, window, controller: Controller) -> None:  # type: ignore[no-untyped-def]
        self.user_profile.setup(window, controller)

    def set_logged_in_as(self, db_user: User) -> None:
        """
        Update the UI to reflect that the user is logged in as "username".
        """
        self.user_profile.set_user(db_user)
        self.user_profile.show()
        self.branding_barre.setPixmap(load_image("left_pane.svg"))

    def set_logged_out(self) -> None:
        """
        Update the UI to a logged out state.
        """
        self.user_profile.hide()
        self.branding_barre.setPixmap(load_image("left_pane_offline.svg"))
