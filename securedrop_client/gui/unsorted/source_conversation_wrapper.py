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
from typing import Optional

from PyQt5.QtCore import pyqtSlot
from PyQt5.QtGui import QBrush, QColor, QPalette
from PyQt5.QtWidgets import QVBoxLayout, QWidget

from securedrop_client import state
from securedrop_client.db import Source
from securedrop_client.gui.unsorted.conversation_deletion_indicator import (
    ConversationDeletionIndicator,
)
from securedrop_client.gui.unsorted.conversation_view import ConversationView
from securedrop_client.gui.unsorted.reply_box_widget import ReplyBoxWidget
from securedrop_client.gui.unsorted.source_deletion_indicator import SourceDeletionIndicator
from securedrop_client.gui.unsorted.source_profile_short_widget import SourceProfileShortWidget
from securedrop_client.logic import Controller
from securedrop_client.resources import load_css

logger = logging.getLogger(__name__)


class SourceConversationWrapper(QWidget):
    """
    Wrapper for a source's conversation including the chat window, profile tab, and other
    per-source resources.
    """

    deleting_conversation = False

    def __init__(
        self,
        source: Source,
        controller: Controller,
        app_state: Optional[state.State] = None,
    ) -> None:
        super().__init__()

        self.setObjectName("SourceConversationWrapper")

        self.source = source
        self.source_uuid = source.uuid
        controller.conversation_deleted.connect(self.on_conversation_deleted)
        controller.conversation_deletion_failed.connect(self.on_conversation_deletion_failed)
        controller.conversation_deletion_successful.connect(
            self._on_conversation_deletion_successful
        )
        controller.source_deleted.connect(self.on_source_deleted)
        controller.source_deletion_failed.connect(self.on_source_deletion_failed)

        # Set layout
        layout = QVBoxLayout()
        self.setLayout(layout)

        # Set margins and spacing
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Create widgets
        self.conversation_title_bar = SourceProfileShortWidget(source, controller, app_state)
        self.conversation_view = ConversationView(source, controller)
        self.reply_box = ReplyBoxWidget(source, controller)
        self.deletion_indicator = SourceDeletionIndicator()
        self.conversation_deletion_indicator = ConversationDeletionIndicator()

        # Add widgets
        layout.addWidget(self.conversation_title_bar)
        layout.addWidget(self.conversation_view)
        layout.addWidget(self.deletion_indicator)
        layout.addWidget(self.conversation_deletion_indicator)
        layout.addWidget(self.reply_box)

        # Connect reply_box to conversation_view
        self.reply_box.reply_sent.connect(self.conversation_view.on_reply_sent)
        self.conversation_view.conversation_updated.connect(self.on_conversation_updated)

    @pyqtSlot(str)
    def on_conversation_deleted(self, source_uuid: str) -> None:
        if self.source_uuid == source_uuid:
            self.start_conversation_deletion()

    @pyqtSlot(str, datetime)
    def _on_conversation_deletion_successful(self, source_uuid: str, timestamp: datetime) -> None:
        if self.source_uuid == source_uuid:
            self.end_conversation_deletion()

    @pyqtSlot(str)
    def on_conversation_deletion_failed(self, source_uuid: str) -> None:
        if self.source_uuid == source_uuid:
            self.end_conversation_deletion()

    @pyqtSlot()
    def on_conversation_updated(self) -> None:
        self.conversation_title_bar.update_timestamp()

    @pyqtSlot(str)
    def on_source_deleted(self, source_uuid: str) -> None:
        if self.source_uuid == source_uuid:
            self.start_account_deletion()

    @pyqtSlot(str)
    def on_source_deletion_failed(self, source_uuid: str) -> None:
        if self.source_uuid == source_uuid:
            self.end_account_deletion()

    def start_conversation_deletion(self) -> None:
        self.reply_box.setProperty("class", "deleting_conversation")
        self.deleting_conversation = True
        self.start_deletion()
        self.conversation_deletion_indicator.start()
        self.deletion_indicator.stop()

    def start_account_deletion(self) -> None:
        self.reply_box.setProperty("class", "deleting")
        self.reply_box.text_edit.setText("")
        self.start_deletion()

        palette = QPalette()
        palette.setBrush(QPalette.Background, QBrush(QColor("#9495b9")))
        palette.setBrush(QPalette.Foreground, QBrush(QColor("#ffffff")))

        self.conversation_title_bar.setPalette(palette)
        self.conversation_title_bar.setAutoFillBackground(True)

        self.conversation_deletion_indicator.stop()
        self.deletion_indicator.start()

    def start_deletion(self) -> None:
        css = load_css("sdclient.css")
        self.reply_box.setStyleSheet(css)
        self.setStyleSheet(css)

        self.reply_box.text_edit.setDisabled(True)
        self.reply_box.text_edit.hide()
        self.reply_box.send_button.setDisabled(True)
        self.conversation_title_bar.setDisabled(True)
        self.conversation_view.hide()

    def end_conversation_deletion(self) -> None:
        self.deleting_conversation = False
        self.end_deletion()

    def end_account_deletion(self) -> None:
        self.end_deletion()

    def end_deletion(self) -> None:
        self.reply_box.setProperty("class", "")
        css = load_css("sdclient.css")
        self.reply_box.setStyleSheet(css)
        self.setStyleSheet(css)

        self.reply_box.text_edit.setEnabled(True)
        self.reply_box.text_edit.show()
        self.reply_box.send_button.setEnabled(True)
        self.conversation_title_bar.setEnabled(True)
        self.conversation_view.show()

        self.conversation_deletion_indicator.stop()
        self.deletion_indicator.stop()
