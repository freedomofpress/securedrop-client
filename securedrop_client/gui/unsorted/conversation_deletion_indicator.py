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

from PyQt5.QtCore import QSize, Qt
from PyQt5.QtGui import QBrush, QColor, QPalette
from PyQt5.QtWidgets import QGridLayout, QLabel, QWidget

from securedrop_client.resources import load_movie

logger = logging.getLogger(__name__)


class ConversationDeletionIndicator(QWidget):
    """
    Shown when a source's conversation content is being deleted.
    """

    def __init__(self) -> None:
        super().__init__()

        self.hide()

        self.setObjectName("ConversationDeletionIndicator")

        palette = QPalette()
        palette.setBrush(QPalette.Background, QBrush(QColor("#9495b9")))
        palette.setBrush(QPalette.Foreground, QBrush(QColor("#ffffff")))
        self.setPalette(palette)
        self.setAutoFillBackground(True)

        deletion_message = QLabel(_("Deleting files and messages…"))
        deletion_message.setWordWrap(False)

        self.animation = load_movie("loading-cubes.gif")
        self.animation.setScaledSize(QSize(50, 50))

        spinner = QLabel()
        spinner.setMovie(self.animation)

        layout = QGridLayout()
        layout.setContentsMargins(20, 20, 20, 20)
        layout.setSpacing(0)
        layout.addWidget(deletion_message, 0, 0, Qt.AlignRight | Qt.AlignVCenter)
        layout.addWidget(spinner, 0, 1, Qt.AlignLeft | Qt.AlignVCenter)
        layout.setColumnStretch(0, 9)
        layout.setColumnStretch(1, 7)

        self.setLayout(layout)

    def start(self) -> None:
        self.animation.start()
        self.show()

    def stop(self) -> None:
        self.animation.stop()
        self.hide()
