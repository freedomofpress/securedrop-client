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

from PyQt5.QtWidgets import QPushButton

logger = logging.getLogger(__name__)


class LoginButton(QPushButton):
    """
    A button that opens a login dialog when clicked.
    """

    def __init__(self) -> None:
        super().__init__(_("SIGN IN"))

        # Set css id
        self.setObjectName("LoginButton")

        self.setFixedHeight(40)

        # Set click handler
        self.clicked.connect(self._on_clicked)

    def setup(self, window) -> None:  # type: ignore[no-untyped-def]
        """
        Store a reference to the GUI window object.
        """
        self._window = window

    def _on_clicked(self) -> None:
        """
        Called when the login button is clicked.
        """
        self._window.show_login()
