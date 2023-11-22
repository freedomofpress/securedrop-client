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
from uuid import uuid4

import sqlalchemy.orm.exc
from PyQt5.QtCore import QSize, Qt, pyqtSignal, pyqtSlot
from PyQt5.QtGui import QCursor, QIcon, QKeySequence
from PyQt5.QtWidgets import QHBoxLayout, QPushButton, QSizePolicy, QVBoxLayout, QWidget

from securedrop_client.db import Source
from securedrop_client.gui.unsorted.reply_text_edit import ReplyTextEdit
from securedrop_client.logic import Controller
from securedrop_client.resources import load_image

logger = logging.getLogger(__name__)


class ReplyBoxWidget(QWidget):
    """
    A textbox where a journalist can enter a reply.
    """

    reply_sent = pyqtSignal(str)

    def __init__(self, source: Source, controller: Controller) -> None:
        super().__init__()

        self.source = source
        self.controller = controller

        # Set css id
        self.setObjectName("ReplyBoxWidget")

        # Set layout
        main_layout = QVBoxLayout()
        self.setLayout(main_layout)

        # Set margins
        main_layout.setContentsMargins(0, 0, 0, 0)
        main_layout.setSpacing(0)

        # Create top horizontal line
        horizontal_line = QWidget()
        horizontal_line.setObjectName("ReplyBoxWidget_horizontal_line")
        horizontal_line.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        # Create replybox
        self.replybox = QWidget()
        self.replybox.setObjectName("ReplyBoxWidget_replybox")
        replybox_layout = QHBoxLayout(self.replybox)
        replybox_layout.setContentsMargins(32, 19, 28, 18)
        replybox_layout.setSpacing(0)

        # Create reply text box
        self.text_edit = ReplyTextEdit(self.source, self.controller)

        # Create reply send button (airplane)
        self.send_button = QPushButton()
        self.send_button.setObjectName("ReplyBoxWidget_send_button")
        self.send_button.clicked.connect(self.send_reply)
        send_button_icon = QIcon(load_image("send.svg"))
        send_button_icon.addPixmap(load_image("send-disabled.svg"), QIcon.Disabled)
        self.send_button.setIcon(send_button_icon)
        self.send_button.setIconSize(QSize(56, 47))
        self.send_button.setShortcut(QKeySequence("Ctrl+Return"))
        self.send_button.setDefault(True)

        # Set cursor.
        self.send_button.setCursor(QCursor(Qt.PointingHandCursor))

        # Add widgets to replybox
        replybox_layout.addWidget(self.text_edit)
        replybox_layout.addWidget(self.send_button, alignment=Qt.AlignBottom)

        # Ensure TAB order from text edit -> send button
        self.setTabOrder(self.text_edit, self.send_button)

        # Add widgets
        main_layout.addWidget(horizontal_line)
        main_layout.addWidget(self.replybox)

        # Determine whether or not this widget should be rendered in offline mode
        self.update_authentication_state(self.controller.is_authenticated)

        # Text area refocus flag.
        self.refocus_after_sync = False

        # Connect signals to slots
        self.controller.authentication_state.connect(self._on_authentication_changed)
        self.controller.sync_started.connect(self._on_sync_started)
        self.controller.sync_succeeded.connect(self._on_sync_succeeded)

    def set_logged_in(self) -> None:
        self.text_edit.set_logged_in()
        # Even if we are logged in, we cannot reply to a source if we do not
        # have a public key for it.
        if self.source.public_key:
            self.replybox.setEnabled(True)
            self.send_button.show()
        else:
            self.replybox.setEnabled(False)
            self.send_button.hide()

    def set_logged_out(self) -> None:
        self.text_edit.set_logged_out()
        self.replybox.setEnabled(False)
        self.send_button.hide()

    def send_reply(self) -> None:
        """
        Send reply and emit a signal so that the gui can be updated immediately indicating
        that it is a pending reply.
        """
        reply_text = self.text_edit.toPlainText().strip()
        if reply_text:
            self.text_edit.clearFocus()  # Fixes #691
            self.text_edit.setText("")
            reply_uuid = str(uuid4())
            self.controller.send_reply(self.source.uuid, reply_uuid, reply_text)
            self.reply_sent.emit(self.source.uuid)

    @pyqtSlot(bool)
    def _on_authentication_changed(self, authenticated: bool) -> None:
        try:
            self.update_authentication_state(authenticated)
        except sqlalchemy.orm.exc.ObjectDeletedError:
            logger.debug(
                "On authentication change, ReplyBoxWidget found its source had been deleted."
            )
            self.destroy()

    def update_authentication_state(self, authenticated: bool) -> None:
        if authenticated:
            self.set_logged_in()
        else:
            self.set_logged_out()

    @pyqtSlot(datetime)
    def _on_sync_started(self, timestamp: datetime) -> None:
        try:
            self.update_authentication_state(self.controller.is_authenticated)
            if self.text_edit.hasFocus():
                self.refocus_after_sync = True
            else:
                self.refocus_after_sync = False
        except sqlalchemy.orm.exc.ObjectDeletedError as e:
            logger.debug(f"During sync, ReplyBoxWidget found its source had been deleted: {e}")
            self.destroy()

    @pyqtSlot()
    def _on_sync_succeeded(self) -> None:
        try:
            self.update_authentication_state(self.controller.is_authenticated)
            # TODO: Handle edge case where a user starts out with the reply box in focus at the
            # beginning of a sync, but then switches to another reply box before the sync finishes.
            if self.refocus_after_sync:
                self.text_edit.setFocus()
            else:
                self.refocus_after_sync = False
        except sqlalchemy.orm.exc.ObjectDeletedError as e:
            logger.debug(f"During sync, ReplyBoxWidget found its source had been deleted: {e}")
            self.destroy()
