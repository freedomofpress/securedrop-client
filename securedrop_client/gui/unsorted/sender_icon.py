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

from PyQt5.QtCore import QSize, Qt
from PyQt5.QtGui import QFont
from PyQt5.QtWidgets import QLabel, QVBoxLayout, QWidget

from securedrop_client.resources import load_css, load_image

logger = logging.getLogger(__name__)


class SenderIcon(QWidget):
    """
    Represents a reply to a source.
    """

    SENDER_ICON_CSS = load_css("sender_icon.css")

    def __init__(self) -> None:
        super().__init__()
        self._is_current_user = False
        self._initials = ""
        self.setObjectName("SenderIcon")
        self.setStyleSheet(self.SENDER_ICON_CSS)
        self.setFixedSize(QSize(48, 48))
        font = QFont()
        font.setLetterSpacing(QFont.AbsoluteSpacing, 0.58)
        self.label = QLabel()
        self.label.setAlignment(Qt.AlignCenter)
        self.label.setFont(font)
        layout = QVBoxLayout()
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)
        layout.addWidget(self.label)
        self.setLayout(layout)

    @property
    def is_current_user(self) -> bool:
        return self._is_current_user

    @is_current_user.setter
    def is_current_user(self, is_current_user: bool) -> None:
        if self._is_current_user != is_current_user:
            self._is_current_user = is_current_user

    @property
    def initials(self) -> str:
        return self._initials

    @initials.setter
    def initials(self, initials: str) -> None:
        if not initials:
            self.label.setPixmap(load_image("deleted-user.svg"))
        else:
            self.label.setText(initials)

        if self._initials != initials:
            self._initials = initials

    def set_normal_styles(self) -> None:
        self.setStyleSheet("")
        if self.is_current_user:
            self.setObjectName("SenderIcon_current_user")
        else:
            self.setObjectName("SenderIcon")
        self.setStyleSheet(self.SENDER_ICON_CSS)

    def set_failed_styles(self) -> None:
        self.setStyleSheet("")
        self.setObjectName("SenderIcon_failed")
        self.setStyleSheet(self.SENDER_ICON_CSS)

    def set_pending_styles(self) -> None:
        self.setStyleSheet("")
        if self.is_current_user:
            self.setObjectName("SenderIcon_current_user_pending")
        else:
            self.setObjectName("SenderIcon_pending")
        self.setStyleSheet(self.SENDER_ICON_CSS)

    def set_failed_to_decrypt_styles(self) -> None:
        self.setStyleSheet("")
        self.setObjectName("SenderIcon_failed_to_decrypt")
        self.setStyleSheet(self.SENDER_ICON_CSS)
