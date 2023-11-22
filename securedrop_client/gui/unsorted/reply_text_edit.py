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
from PyQt5.QtGui import QCursor, QFocusEvent, QResizeEvent
from PyQt5.QtWidgets import QPlainTextEdit

from securedrop_client.db import Source
from securedrop_client.gui.unsorted.reply_text_edit_placeholder import ReplyTextEditPlaceholder
from securedrop_client.logic import Controller

logger = logging.getLogger(__name__)


class ReplyTextEdit(QPlainTextEdit):
    """
    A plaintext textbox with placeholder that disappears when clicked and
    a richtext label on top to replace the placeholder functionality
    """

    def __init__(self, source: Source, controller: Controller) -> None:
        super().__init__()

        self.controller = controller
        self.source = source

        self.setObjectName("ReplyTextEdit")

        retain_space = self.sizePolicy()
        retain_space.setRetainSizeWhenHidden(True)
        self.setSizePolicy(retain_space)

        self.setVerticalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.setTabChangesFocus(True)  # Needed so we can TAB to send button.
        self.setCursor(QCursor(Qt.IBeamCursor))

        self.placeholder = ReplyTextEditPlaceholder(source.journalist_designation)
        self.placeholder.setParent(self)

        self.set_logged_in()

    def focusInEvent(self, e: QFocusEvent) -> None:
        # override default behavior: when reply text box is focused, the placeholder
        # disappears instead of only doing so when text is typed
        if self.toPlainText() == "":
            self.placeholder.hide()
        super(ReplyTextEdit, self).focusInEvent(e)

    def focusOutEvent(self, e: QFocusEvent) -> None:
        if self.toPlainText() == "":
            self.placeholder.show()
        super(ReplyTextEdit, self).focusOutEvent(e)

    def set_logged_in(self) -> None:
        if self.source.public_key:
            self.placeholder.show_signed_in()
            self.setEnabled(True)
        else:
            self.placeholder.show_signed_in_no_key()
            self.setEnabled(False)

    def set_logged_out(self) -> None:
        self.placeholder.show_signed_out()
        self.setEnabled(False)

    def setText(self, text: str) -> None:
        if text == "":
            self.placeholder.show()
        else:
            self.placeholder.hide()
        super(ReplyTextEdit, self).setPlainText(text)

    def resizeEvent(self, event: QResizeEvent) -> None:
        # Adjust available source label width to elide text when necessary
        self.placeholder.update_label_width(event.size().width())
        super().resizeEvent(event)
