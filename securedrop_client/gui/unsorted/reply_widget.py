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
from typing import Optional

import sqlalchemy.orm.exc
from PyQt5.QtCore import QSize, Qt, pyqtSlot
from PyQt5.QtWidgets import QHBoxLayout, QWidget

from securedrop_client.db import ReplySendStatusCodes, User
from securedrop_client.gui.base import SecureQLabel, SvgLabel
from securedrop_client.gui.unsorted.speech_bubble import SpeechBubble
from securedrop_client.logic import Controller
from securedrop_client.resources import load_css

logger = logging.getLogger(__name__)


class ReplyWidget(SpeechBubble):
    """
    Represents a reply to a source.
    """

    MESSAGE_CSS = load_css("speech_bubble_message.css")
    STATUS_BAR_CSS = load_css("speech_bubble_status_bar.css")

    ERROR_BOTTOM_MARGIN = 20

    def __init__(  # type: ignore[no-untyped-def]
        self,
        controller: Controller,
        message_uuid: str,
        message: str,
        reply_status: str,
        update_signal,
        download_error_signal,
        message_succeeded_signal,
        message_failed_signal,
        index: int,
        container_width: int,
        sender: User,
        sender_is_current_user: bool,
        authenticated_user: Optional[User] = None,
        failed_to_decrypt: bool = False,
    ) -> None:
        super().__init__(
            message_uuid,
            message,
            update_signal,
            download_error_signal,
            index,
            container_width,
            authenticated_user,
            failed_to_decrypt,
        )
        self.controller = controller
        self.status = reply_status
        self.uuid = message_uuid
        self._sender = sender
        self._sender_is_current_user = sender_is_current_user
        self.failed_to_decrypt = failed_to_decrypt

        self.error = QWidget()
        error_layout = QHBoxLayout()
        error_layout.setContentsMargins(0, 0, 0, self.ERROR_BOTTOM_MARGIN)
        error_layout.setSpacing(4)
        self.error.setLayout(error_layout)
        error_message = SecureQLabel(_("Failed to send"), wordwrap=False)
        error_message.setObjectName("ReplyWidget_failed_to_send_text")
        error_icon = SvgLabel("error_icon.svg", svg_size=QSize(12, 12))
        error_icon.setFixedWidth(12)
        error_layout.addWidget(error_message)
        error_layout.addWidget(error_icon)
        retain_space = self.sizePolicy()
        retain_space.setRetainSizeWhenHidden(True)
        self.error.setSizePolicy(retain_space)
        self.error.hide()

        self.bubble_area_layout.addWidget(self.check_mark, alignment=Qt.AlignBottom)
        self.bubble_area_layout.addWidget(self.error, alignment=Qt.AlignBottom)
        self.sender_icon.show()

        self.check_mark.show()

        update_signal.connect(self._on_reply_success)
        message_succeeded_signal.connect(self._on_reply_success)
        message_failed_signal.connect(self._on_reply_failure)
        self.controller.update_authenticated_user.connect(self._on_update_authenticated_user)
        self.controller.authentication_state.connect(self._on_authentication_changed)

        self.sender_icon.is_current_user = self._sender_is_current_user
        if self._sender:
            self.sender_icon.initials = self._sender.initials
            self.sender_icon.setToolTip(self._sender.fullname)
        self._update_styles()

    @property
    def sender_is_current_user(self) -> bool:
        return self._sender_is_current_user

    @sender_is_current_user.setter
    def sender_is_current_user(self, sender_is_current_user: bool) -> None:
        if self._sender_is_current_user != sender_is_current_user:
            self._sender_is_current_user = sender_is_current_user
            self.sender_icon.is_current_user = sender_is_current_user

    @property
    def sender(self) -> User:
        return self._sender

    @sender.setter
    def sender(self, sender: User) -> None:
        if self._sender != sender:
            self._sender = sender

        if self._sender:
            self.sender_icon.initials = self._sender.initials
            self.sender_icon.setToolTip(self._sender.fullname)

    @pyqtSlot(bool)
    def _on_authentication_changed(self, authenticated: bool) -> None:
        """
        When the user logs out, update the reply badge.
        """
        if not authenticated:
            self.sender_is_current_user = False
            self._update_styles()

    @pyqtSlot(User)
    def _on_update_authenticated_user(self, user: User) -> None:
        """
        When the user logs in or updates user info, update the reply badge.
        """
        try:
            if self.sender and self.sender.uuid == user.uuid:
                self.sender_is_current_user = True
                self.sender = user
                self.sender_icon.setToolTip(self.sender.fullname)
                self._update_styles()
        except sqlalchemy.orm.exc.ObjectDeletedError:
            logger.debug("The sender was deleted.")

    @pyqtSlot(str, str, str)
    def _on_reply_success(self, source_uuid: str, uuid: str, content: str) -> None:
        """
        Conditionally update this ReplyWidget's state if and only if the message_uuid of the emitted
        signal matches the uuid of this widget.
        """
        if self.uuid == uuid:
            self.status = "SUCCEEDED"  # TODO: Add and use success status in db.ReplySendStatusCodes
            self.failed_to_decrypt = False
            self._update_styles()

    @pyqtSlot(str)
    def _on_reply_failure(self, uuid: str) -> None:
        """
        Conditionally update this ReplyWidget's state if and only if the message_uuid of the emitted
        signal matches the uuid of this widget.
        """
        if self.uuid == uuid:
            self.status = ReplySendStatusCodes.FAILED.value
            self.failed_to_decrypt = False
            self._update_styles()

    def _update_styles(self) -> None:
        if self.failed_to_decrypt:
            self.set_failed_to_decrypt_styles()
        elif self.status == ReplySendStatusCodes.PENDING.value:
            self.set_pending_styles()
            self.check_mark.hide()
        elif self.status == ReplySendStatusCodes.FAILED.value:
            self.set_failed_styles()
            self.error.show()
            self.check_mark.hide()
        else:
            self.set_normal_styles()
            self.error.hide()
            self.check_mark.show()

    def set_normal_styles(self) -> None:
        self.message.setStyleSheet("")
        self.message.setObjectName("SpeechBubble_reply")
        self.message.setStyleSheet(self.MESSAGE_CSS)

        self.sender_icon.set_normal_styles()

        self.color_bar.setStyleSheet("")
        if self.sender_is_current_user:
            self.color_bar.setObjectName("ReplyWidget_status_bar_current_user")
        else:
            self.color_bar.setObjectName("ReplyWidget_status_bar")
        self.color_bar.setStyleSheet(self.STATUS_BAR_CSS)

    def set_pending_styles(self) -> None:
        self.message.setStyleSheet("")
        self.message.setObjectName("ReplyWidget_message_pending")
        self.message.setStyleSheet(self.MESSAGE_CSS)

        self.sender_icon.set_pending_styles()

        self.color_bar.setStyleSheet("")
        if self.sender_is_current_user:
            self.color_bar.setObjectName("ReplyWidget_status_bar_pending_current_user")
        else:
            self.color_bar.setObjectName("ReplyWidget_status_bar_pending")
        self.color_bar.setStyleSheet(self.STATUS_BAR_CSS)

    def set_failed_styles(self) -> None:
        self.message.setStyleSheet("")
        self.message.setObjectName("ReplyWidget_message_failed")
        self.message.setStyleSheet(self.MESSAGE_CSS)
        self.sender_icon.set_failed_styles()
        self.color_bar.setStyleSheet("")
        self.color_bar.setObjectName("ReplyWidget_status_bar_failed")
        self.color_bar.setStyleSheet(self.STATUS_BAR_CSS)
