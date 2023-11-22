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

from PyQt5.QtGui import QBrush, QColor, QLinearGradient, QPalette
from PyQt5.QtWidgets import QHBoxLayout, QWidget

from securedrop_client.gui.unsorted.activity_status_bar import ActivityStatusBar
from securedrop_client.gui.unsorted.error_status_bar import ErrorStatusBar
from securedrop_client.gui.unsorted.sync_icon import SyncIcon
from securedrop_client.gui.unsorted.sync_status_bar import SyncStatusBar
from securedrop_client.logic import Controller

logger = logging.getLogger(__name__)


class TopPane(QWidget):
    """
    Top pane of the app window.
    """

    def __init__(self) -> None:
        super().__init__()

        # Fill the background with a gradient
        self.online_palette = QPalette()
        gradient = QLinearGradient(0, 0, 1553, 0)
        gradient.setColorAt(0, QColor("#1573d8"))
        gradient.setColorAt(0.22, QColor("#0060d3"))
        gradient.setColorAt(1, QColor("#002c53"))
        self.online_palette.setBrush(QPalette.Background, QBrush(gradient))

        self.offline_palette = QPalette()
        gradient = QLinearGradient(0, 0, 1553, 0)
        gradient.setColorAt(0, QColor("#1e1e1e"))
        gradient.setColorAt(0.22, QColor("#122d61"))
        gradient.setColorAt(1, QColor("#0d4a81"))
        self.offline_palette.setBrush(QPalette.Background, QBrush(gradient))

        self.setPalette(self.offline_palette)
        self.setAutoFillBackground(True)

        # Set layout
        layout = QHBoxLayout(self)
        self.setLayout(layout)

        # Remove margins and spacing
        layout.setContentsMargins(10, 0, 0, 0)
        layout.setSpacing(0)

        # Sync icon
        self.sync_icon = SyncIcon()

        # Sync status bar with fixed width so that the left side of the
        # activity status bar lines up with left pane
        self.sync_status_bar = SyncStatusBar()
        self.sync_status_bar.setFixedWidth(171)

        # Activity status bar
        self.activity_status_bar = ActivityStatusBar()

        # Error status bar
        self.error_status_bar = ErrorStatusBar()

        # Create spacers the size of the sync icon and sync and activity status bars
        # so that the error status bar is centered
        sync_icon_spacer = QWidget()
        sync_icon_spacer.setFixedWidth(42)

        sync_status_bar_spacer = QWidget()
        sync_status_bar_spacer.setFixedWidth(171)

        activity_status_bar_spacer = QWidget()

        # Set height of top pane to 42 pixels
        self.setFixedHeight(42)
        self.sync_icon.setFixedHeight(42)
        self.activity_status_bar.setFixedHeight(42)
        self.error_status_bar.setFixedHeight(42)

        # Add widgets to layout
        layout.addWidget(self.sync_icon, 1)
        layout.addWidget(self.sync_status_bar, 1)
        layout.addWidget(self.activity_status_bar, 1)

        layout.addWidget(self.error_status_bar, 1)

        layout.addWidget(activity_status_bar_spacer, 1)
        layout.addWidget(sync_status_bar_spacer, 1)
        layout.addWidget(sync_icon_spacer, 1)

    def setup(self, controller: Controller) -> None:
        self.sync_icon.setup(controller)
        self.error_status_bar.setup(controller)

    def set_logged_in(self) -> None:
        self.sync_icon.enable()
        self.setPalette(self.online_palette)

    def set_logged_out(self) -> None:
        self.sync_icon.disable()
        self.setPalette(self.offline_palette)

    def update_sync_status(self, message: str, duration: int) -> None:
        self.sync_status_bar.update_message(message, duration)

    def update_activity_status(self, message: str, duration: int) -> None:
        self.activity_status_bar.update_message(message, duration)

    def update_error_status(self, message: str, duration: int) -> None:
        self.error_status_bar.update_message(message, duration)

    def clear_error_status(self) -> None:
        self.error_status_bar.clear_message()
