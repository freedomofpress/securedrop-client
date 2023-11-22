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

from PyQt5.QtCore import QSize
from PyQt5.QtWidgets import QHBoxLayout, QPushButton

from securedrop_client.resources import load_css, load_icon

logger = logging.getLogger(__name__)


class CheckMark(QPushButton):
    """
    Represents the seen by checkmark for each bubble.
    """

    CHECK_MARK_CSS = load_css("checker_tooltip.css")
    CLICKABLE_SPACE = 65

    def __init__(self) -> None:
        super().__init__()
        self.setObjectName("Checker")
        self.setStyleSheet(self.CHECK_MARK_CSS)
        layout = QHBoxLayout()
        self.setIcon(load_icon("checkmark.svg"))
        self.setIconSize(QSize(16, 10))
        layout.setSpacing(self.CLICKABLE_SPACE)
        self.setLayout(layout)
