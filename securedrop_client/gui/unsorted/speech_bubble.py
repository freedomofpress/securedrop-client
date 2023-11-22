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
from typing import Dict, Optional

from PyQt5.QtCore import QEvent, QObject, Qt, pyqtSlot
from PyQt5.QtWidgets import QHBoxLayout, QVBoxLayout, QWidget

from securedrop_client.db import User
from securedrop_client.gui.base import SecureQLabel
from securedrop_client.gui.unsorted.check_mark import CheckMark
from securedrop_client.gui.unsorted.sender_icon import SenderIcon
from securedrop_client.resources import load_css, load_icon

logger = logging.getLogger(__name__)


class SpeechBubble(QWidget):
    """
    Represents a speech bubble that's part of a conversation between a source
    and journalist.
    """

    MESSAGE_CSS = load_css("speech_bubble_message.css")
    STATUS_BAR_CSS = load_css("speech_bubble_status_bar.css")
    CHECK_MARK_CSS = load_css("checker_tooltip.css")

    WIDTH_TO_CONTAINER_WIDTH_RATIO = 5 / 9
    MIN_WIDTH = 400
    MIN_CONTAINER_WIDTH = 750

    TOP_MARGIN = 28
    BOTTOM_MARGIN = 0

    def __init__(  # type: ignore[no-untyped-def]
        self,
        message_uuid: str,
        text: str,
        update_signal,
        download_error_signal,
        index: int,
        container_width: int,
        authenticated_user: Optional[User] = None,
        failed_to_decrypt: bool = False,
    ) -> None:
        super().__init__()
        self.uuid = message_uuid
        self.index = index
        self.authenticated_user = authenticated_user
        self.seen_by: Dict[str, User] = {}

        # Add the authenticated user as the default value of the dictionary
        # that will initialize the tooltip.
        if self.authenticated_user:
            self.seen_by[self.authenticated_user.username] = self.authenticated_user

        self.failed_to_decrypt = failed_to_decrypt

        # Set layout
        layout = QVBoxLayout()
        self.setLayout(layout)

        # Set margins and spacing
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Message box
        self.message = SecureQLabel(text)
        self.message.setObjectName("SpeechBubble_message")
        self.message.setStyleSheet(self.MESSAGE_CSS)

        # Color bar
        self.color_bar = QWidget()
        self.color_bar.setObjectName("SpeechBubble_status_bar")
        self.color_bar.setStyleSheet(self.STATUS_BAR_CSS)

        # User icon
        self.sender_icon = SenderIcon()
        self.sender_icon.hide()

        # Check mark
        self.check_mark = CheckMark()
        self.setObjectName("Checker")
        self.setStyleSheet(self.CHECK_MARK_CSS)
        self.check_mark.installEventFilter(self)

        # Speech bubble
        self.speech_bubble = QWidget()
        speech_bubble_layout = QVBoxLayout()
        self.speech_bubble.setLayout(speech_bubble_layout)
        speech_bubble_layout.addWidget(self.message)
        speech_bubble_layout.addWidget(self.color_bar)
        speech_bubble_layout.setContentsMargins(0, 0, 0, 0)
        speech_bubble_layout.setSpacing(0)

        # Bubble area includes speech bubble plus error message if there is an error
        self.bubble_area = QWidget()
        self.bubble_area.setLayoutDirection(Qt.RightToLeft)
        self.bubble_area_layout = QHBoxLayout()
        self.bubble_area_layout.setContentsMargins(0, self.TOP_MARGIN, 0, self.BOTTOM_MARGIN)
        self.bubble_area.setLayout(self.bubble_area_layout)
        self.bubble_area_layout.addWidget(self.sender_icon, alignment=Qt.AlignBottom)
        self.bubble_area_layout.addWidget(self.speech_bubble)

        # Add widget to layout
        layout.addWidget(self.bubble_area)

        # Make text selectable but disable the context menu
        self.message.setTextInteractionFlags(Qt.TextSelectableByMouse)
        self.message.setContextMenuPolicy(Qt.NoContextMenu)

        if self.failed_to_decrypt:
            self.set_failed_to_decrypt_styles()

        # Connect signals to slots
        update_signal.connect(self._update_text)
        download_error_signal.connect(self._on_download_error)

        # Set checkmark tooltip to the default seen_by list
        self.update_seen_by_list(self.seen_by)

        self.adjust_width(container_width)

    def adjust_width(self, container_width: int) -> None:
        """
        This is a workaround to the workaround for https://bugreports.qt.io/browse/QTBUG-85498.
        Since QLabels containing text with long strings that cannot be wrapped have to have a fixed
        width in order to fit within the scrollarea widget, we have to override the normal resizing
        logic.
        """
        if container_width < self.MIN_CONTAINER_WIDTH:
            self.speech_bubble.setFixedWidth(self.MIN_WIDTH)
        else:
            self.speech_bubble.setFixedWidth(
                int(container_width * self.WIDTH_TO_CONTAINER_WIDTH_RATIO)
            )

    @pyqtSlot(str, str, str)
    def _update_text(self, source_uuid: str, uuid: str, text: str) -> None:
        """
        Conditionally update this SpeechBubble's text if and only if the message_uuid of the emitted
        signal matches the uuid of this speech bubble.
        """
        if self.uuid == uuid:
            self.message.setText(text)
            self.set_normal_styles()

    @pyqtSlot(str, str, str)
    def _on_download_error(self, source_uuid: str, uuid: str, text: str) -> None:
        """
        Adjust style and text to indicate an error.
        """
        if self.uuid == uuid:
            self.message.setText(text)
            self.failed_to_decrypt = True
            self.set_failed_to_decrypt_styles()

    @pyqtSlot(User)
    def on_update_authenticated_user(self, user: User) -> None:
        """
        When the user logs in or updates user info, retrieve their object.
        """
        self.authenticated_user = user
        self.update_seen_by_list(self.seen_by)

    def set_normal_styles(self) -> None:
        self.message.setStyleSheet("")
        self.message.setObjectName("SpeechBubble_message")
        self.message.setStyleSheet(self.MESSAGE_CSS)
        self.color_bar.setStyleSheet("")
        self.color_bar.setObjectName("SpeechBubble_status_bar")
        self.color_bar.setStyleSheet(self.STATUS_BAR_CSS)

    def set_failed_to_decrypt_styles(self) -> None:
        self.message.setStyleSheet("")
        self.message.setObjectName("SpeechBubble_message_decryption_error")
        self.message.setStyleSheet(self.MESSAGE_CSS)
        self.color_bar.setStyleSheet("")
        self.color_bar.setObjectName("SpeechBubble_status_bar_decryption_error")
        self.color_bar.setStyleSheet(self.STATUS_BAR_CSS)
        self.sender_icon.set_failed_to_decrypt_styles()

    def update_seen_by_list(self, usernames: Dict[str, User]) -> None:
        # Update the dictionary for the new usernames to be shown in the tooltip.
        self.seen_by.update(usernames)

        # Remove any users who've been deleted
        usernames_to_remove = [i for i in self.seen_by if i not in usernames]
        for i in usernames_to_remove:
            del self.seen_by[i]

        # Re-arrange for the authenticated user's username to be shown at the end of the
        # username list shown in the tooltip.
        if self.authenticated_user:
            if self.authenticated_user.username in self.seen_by:
                del self.seen_by[self.authenticated_user.username]
            self.seen_by[self.authenticated_user.username] = self.authenticated_user

        self.check_mark.setToolTip(",\n".join(username for username in self.seen_by.keys()))

    def eventFilter(self, obj: QObject, event: QEvent) -> bool:
        t = event.type()
        if t == QEvent.HoverEnter:
            self.check_mark.setIcon(load_icon("checkmark_hover.svg"))
        elif t == QEvent.HoverLeave:
            self.check_mark.setIcon(load_icon("checkmark.svg"))

        return QObject.event(obj, event)
