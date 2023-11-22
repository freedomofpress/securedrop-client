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

from PyQt5.QtGui import QFont
from PyQt5.QtWidgets import QAction, QMenu

from securedrop_client.logic import Controller

logger = logging.getLogger(__name__)


class UserMenu(QMenu):
    """A menu next to the journalist username.

    A menu that provides login options.
    """

    def __init__(self) -> None:
        super().__init__()
        self.logout = QAction(_("SIGN OUT"))
        self.logout.setFont(QFont("OpenSans", 10))
        self.addAction(self.logout)
        self.logout.triggered.connect(self._on_logout_triggered)

    def setup(self, controller: Controller) -> None:
        """
        Store a reference to the controller (containing the application logic).
        """
        self.controller = controller

    def _on_logout_triggered(self) -> None:
        """
        Called when the logout button is selected from the menu.
        """
        self.controller.logout()
