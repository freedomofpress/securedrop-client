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
from typing import Optional

from PyQt5.QtCore import QSize, Qt
from PyQt5.QtGui import QCursor
from PyQt5.QtWidgets import QToolButton

from securedrop_client import state
from securedrop_client.db import Source
from securedrop_client.gui.unsorted.source_menu import SourceMenu
from securedrop_client.logic import Controller
from securedrop_client.resources import load_icon

logger = logging.getLogger(__name__)


class SourceMenuButton(QToolButton):
    """An ellipse based source menu button.

    This button is responsible for launching the source menu on click.
    """

    def __init__(
        self,
        source: Source,
        controller: Controller,
        app_state: Optional[state.State],
    ) -> None:
        super().__init__()
        self.controller = controller
        self.source = source

        self.setObjectName("SourceMenuButton")

        self.setIcon(load_icon("ellipsis.svg"))
        self.setIconSize(QSize(22, 33))  # Make it taller than the svg viewBox to increase hitbox

        menu = SourceMenu(self.source, self.controller, app_state)
        self.setMenu(menu)

        self.setPopupMode(QToolButton.InstantPopup)
        # Set cursor.
        self.setCursor(QCursor(Qt.PointingHandCursor))
