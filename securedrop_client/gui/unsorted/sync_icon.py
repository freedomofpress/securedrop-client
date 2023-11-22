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
from datetime import datetime

from PyQt5.QtCore import QSize, pyqtSlot
from PyQt5.QtWidgets import QLabel

from securedrop_client.logic import Controller
from securedrop_client.resources import load_movie

logger = logging.getLogger(__name__)


class SyncIcon(QLabel):
    """
    An icon that shows sync state.
    """

    def __init__(self) -> None:
        # Add svg images to button
        super().__init__()
        self.setObjectName("SyncIcon")
        self.setFixedSize(QSize(24, 20))
        self.sync_animation = load_movie("sync_disabled.gif")
        self.sync_animation.setScaledSize(QSize(24, 20))
        self.setMovie(self.sync_animation)
        self.sync_animation.start()

    def setup(self, controller: Controller) -> None:
        """
        Assign a controller object (containing the application logic).
        """
        self.controller = controller
        self.controller.sync_started.connect(self._on_sync_started)
        self.controller.sync_succeeded.connect(self._on_sync_succeeded)

    @pyqtSlot(datetime)
    def _on_sync_started(self, timestamp: datetime) -> None:
        self.sync_animation = load_movie("sync_active.gif")
        self.sync_animation.setScaledSize(QSize(24, 20))
        self.setMovie(self.sync_animation)
        self.sync_animation.start()

    @pyqtSlot()
    def _on_sync_succeeded(self) -> None:
        self.sync_animation = load_movie("sync.gif")
        self.sync_animation.setScaledSize(QSize(24, 20))
        self.setMovie(self.sync_animation)
        self.sync_animation.start()

    def enable(self) -> None:
        self.sync_animation = load_movie("sync.gif")
        self.sync_animation.setScaledSize(QSize(24, 20))
        self.setMovie(self.sync_animation)
        self.sync_animation.start()

    def disable(self) -> None:
        self.sync_animation = load_movie("sync_disabled.gif")
        self.sync_animation.setScaledSize(QSize(24, 20))
        self.setMovie(self.sync_animation)
        self.sync_animation.start()
