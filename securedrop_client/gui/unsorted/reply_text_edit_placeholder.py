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

from PyQt5.QtWidgets import QHBoxLayout, QLabel, QVBoxLayout, QWidget

from securedrop_client.gui.base import SecureQLabel

logger = logging.getLogger(__name__)


class ReplyTextEditPlaceholder(QWidget):
    # These values are used to determine the width that can be taken up by
    # the source designation as the widget is initialized or the window is
    # resized.
    INITIAL_MAX_WIDTH = 150
    RESERVED_WIDTH = 250

    # We allocate a fixed with to the source designation because its text is
    # dynamically resized, which otherwise causes Qt's layout engine to
    # incorrectly reposition it
    FIXED_LABEL_WIDTH = 800

    def __init__(self, source_name: str) -> None:
        super().__init__()

        # Set layout
        layout = QVBoxLayout()
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)
        self.setLayout(layout)

        # Signed in
        compose_a_reply_to = QLabel(_("Compose a reply to "))
        compose_a_reply_to.setObjectName("ReplyTextEditPlaceholder_text")
        self.source_name = source_name
        self.source_name_label = SecureQLabel(
            source_name, wordwrap=False, max_length=self.INITIAL_MAX_WIDTH
        )
        self.source_name_label.setObjectName("ReplyTextEditPlaceholder_bold_blue")
        self.source_name_label.setFixedWidth(self.FIXED_LABEL_WIDTH)
        self.signed_in = QWidget()
        signed_in_layout = QHBoxLayout()
        signed_in_layout.setSpacing(0)
        self.signed_in.setLayout(signed_in_layout)
        signed_in_layout.addWidget(compose_a_reply_to)
        signed_in_layout.addWidget(self.source_name_label)
        self.signed_in.hide()

        # Awaiting key
        awaiting_key = QLabel(_("Awaiting encryption key"))
        awaiting_key.setObjectName("ReplyTextEditPlaceholder_bold_blue")
        from_server = QLabel(_(" from server to enable replies"))
        from_server.setObjectName("ReplyTextEditPlaceholder_text")
        self.signed_in_no_key = QWidget()
        signed_in_no_key_layout = QHBoxLayout()
        signed_in_no_key_layout.setSpacing(0)
        self.signed_in_no_key.setLayout(signed_in_no_key_layout)
        signed_in_no_key_layout.addWidget(awaiting_key)
        signed_in_no_key_layout.addWidget(from_server)
        self.signed_in_no_key.hide()

        # Signed out
        sign_in = QLabel(_("Sign in"))
        sign_in.setObjectName("ReplyTextEditPlaceholder_bold_blue")
        to_compose_reply = QLabel(_(" to compose or send a reply"))
        to_compose_reply.setObjectName("ReplyTextEditPlaceholder_text")
        self.signed_out = QWidget()
        signed_out_layout = QHBoxLayout()
        signed_out_layout.setSpacing(0)
        self.signed_out.setLayout(signed_out_layout)
        signed_out_layout.addWidget(sign_in)
        signed_out_layout.addWidget(to_compose_reply)
        signed_out_layout.addStretch()
        self.signed_out.hide()

        layout.addWidget(self.signed_in)
        layout.addWidget(self.signed_in_no_key)
        layout.addWidget(self.signed_out)

    def show_signed_in(self) -> None:
        self.signed_in_no_key.hide()
        self.signed_in.show()
        self.signed_out.hide()

    def show_signed_in_no_key(self) -> None:
        self.signed_in_no_key.show()
        self.signed_in.hide()
        self.signed_out.hide()

    def show_signed_out(self) -> None:
        self.signed_in_no_key.hide()
        self.signed_in.hide()
        self.signed_out.show()

    def update_label_width(self, width: int) -> None:
        if width > self.RESERVED_WIDTH:
            # Ensure source designations are elided with "…" if needed per
            # current container size
            self.source_name_label.max_length = width - self.RESERVED_WIDTH
            self.source_name_label.setText(self.source_name)
