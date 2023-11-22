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
from PyQt5.QtWidgets import QLabel

from securedrop_client.resources import load_movie

logger = logging.getLogger(__name__)


class SourceWidgetDeletionIndicator(QLabel):
    """
    Shown in the source list when a source's conversation content is being deleted.
    """

    def __init__(self) -> None:
        super().__init__()

        self.hide()

        self.setObjectName("SourceWidgetDeletionIndicator")

        self.animation = load_movie("loading-bar.gif")
        self.animation.setScaledSize(QSize(200, 11))

        self.setMovie(self.animation)

    def start(self) -> None:
        self.animation.start()
        self.show()

    def stop(self) -> None:
        self.animation.stop()
        self.hide()
