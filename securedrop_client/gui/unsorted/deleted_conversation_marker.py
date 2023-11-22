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
from PyQt5.QtWidgets import QLabel, QSizePolicy, QVBoxLayout, QWidget

from securedrop_client.gui.base import SvgLabel

logger = logging.getLogger(__name__)


class DeletedConversationMarker(QWidget):
    """
    Shown when all content in a conversation has been deleted.
    """

    def __init__(self) -> None:
        super().__init__()

        self.hide()

        self.setObjectName("DeletedConversationMarker")

        deletion_message = QLabel(_("Files and messages deleted\n for this source"))
        deletion_message.setWordWrap(True)
        deletion_message.setAlignment(Qt.AlignCenter)
        deletion_message.setObjectName("DeletedConversationMessage")

        tear = SvgLabel("tear-big.svg", svg_size=QSize(576, 8))
        tear.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        layout = QVBoxLayout()
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(20)

        layout.addStretch()
        layout.addWidget(deletion_message)
        layout.addWidget(tear)
        layout.addStretch()

        self.setLayout(layout)
