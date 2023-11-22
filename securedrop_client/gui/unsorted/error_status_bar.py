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

from PyQt5.QtCore import QSize, QTimer
from PyQt5.QtWidgets import QHBoxLayout, QStatusBar, QWidget

from securedrop_client.gui.base import SvgLabel
from securedrop_client.logic import Controller

logger = logging.getLogger(__name__)


class ErrorStatusBar(QWidget):
    """
    A pop-up status bar for displaying messages about application errors to the user. Messages will
    be displayed for a given duration or until the message is cleared or updated with a new message.
    """

    def __init__(self) -> None:
        super().__init__()

        # Set layout
        layout = QHBoxLayout(self)
        self.setLayout(layout)

        # Remove margins and spacing
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Error vertical bar
        self.vertical_bar = QWidget()
        self.vertical_bar.setObjectName("ErrorStatusBar_vertical_bar")  # Set css id
        self.vertical_bar.setFixedWidth(10)

        # Error icon
        self.label = SvgLabel("error_icon.svg", svg_size=QSize(20, 20))
        self.label.setObjectName("ErrorStatusBar_icon")  # Set css id
        self.label.setFixedWidth(42)

        # Error status bar
        self.status_bar = QStatusBar()
        self.status_bar.setObjectName("ErrorStatusBar_status_bar")  # Set css id
        self.status_bar.setSizeGripEnabled(False)

        # Add widgets to layout
        layout.addWidget(self.vertical_bar)
        layout.addWidget(self.label)
        layout.addWidget(self.status_bar)

        # Hide until a message needs to be displayed
        self.vertical_bar.hide()
        self.label.hide()
        self.status_bar.hide()

        # Only show errors for a set duration
        self.status_timer = QTimer()
        self.status_timer.timeout.connect(self._on_status_timeout)

    def _hide(self) -> None:
        self.vertical_bar.hide()
        self.label.hide()
        self.status_bar.hide()

    def _show(self) -> None:
        self.vertical_bar.show()
        self.label.show()
        self.status_bar.show()

    def _on_status_timeout(self) -> None:
        self._hide()

    def setup(self, controller: Controller) -> None:
        self.controller = controller

    def update_message(self, message: str, duration: int) -> None:
        """
        Display a status message to the user for a given duration. If the duration is zero,
        continuously show message.
        """
        self.status_bar.showMessage(message, duration)
        new_width = self.fontMetrics().horizontalAdvance(message)
        self.status_bar.setMinimumWidth(new_width)
        self.status_bar.reformat()

        if duration != 0:
            self.status_timer.start(duration)

        self._show()

    def clear_message(self) -> None:
        """
        Clear any message currently in the status bar.
        """
        self.status_bar.clearMessage()
        self._hide()
