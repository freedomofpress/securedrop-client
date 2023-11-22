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

from PyQt5.QtCore import Qt
from PyQt5.QtGui import QResizeEvent
from PyQt5.QtWidgets import QScrollArea, QSizePolicy, QVBoxLayout, QWidget

from securedrop_client.gui.unsorted.file_widget import FileWidget
from securedrop_client.gui.unsorted.speech_bubble import SpeechBubble

logger = logging.getLogger(__name__)


class ConversationScrollArea(QScrollArea):
    MARGIN_BOTTOM = 28
    MARGIN_LEFT = 38
    MARGIN_RIGHT = 20

    def __init__(self) -> None:
        super().__init__()

        self.setWidgetResizable(True)

        self.setObjectName("ConversationScrollArea")

        # Create the scroll area's widget
        conversation = QWidget()
        conversation.setObjectName("ConversationScrollArea_conversation")
        # The size policy for the scrollarea's widget needs a fixed height so that the speech
        # bubbles are aligned at the top rather than spreading out to fill the height of the
        # scrollarea.
        conversation.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        self.conversation_layout = QVBoxLayout()
        conversation.setLayout(self.conversation_layout)
        self.conversation_layout.setContentsMargins(
            self.MARGIN_LEFT, 0, self.MARGIN_RIGHT, self.MARGIN_BOTTOM
        )
        self.conversation_layout.setSpacing(0)

        # `conversation` is a child of this scroll area
        self.setWidget(conversation)

    def resizeEvent(self, event: QResizeEvent) -> None:
        """
        This is a workaround to the workaround for https://bugreports.qt.io/browse/QTBUG-85498.
        See comment in the adjust_width method for SpeechBubble.
        """
        super().resizeEvent(event)
        self.widget().setFixedWidth(event.size().width())

        for file_widget in self.findChildren(FileWidget):
            file_widget.adjust_width(self.widget().width())

        for widget in self.findChildren(SpeechBubble):
            widget.adjust_width(self.widget().width())

    def add_widget_to_conversation(
        self, index: int, widget: QWidget, alignment_flag: Qt.AlignmentFlag
    ) -> None:
        """
        Add `widget` to the scroll area's widget layout.
        """
        self.conversation_layout.insertWidget(index, widget, alignment=alignment_flag)

    def remove_widget_from_conversation(self, widget: QWidget) -> None:
        """
        Remove `widget` from the scroll area's widget layout.
        """
        self.conversation_layout.removeWidget(widget)
