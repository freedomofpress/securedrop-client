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
from PyQt5.QtWidgets import QGridLayout, QLabel, QSizePolicy, QWidget

from securedrop_client.gui.base import SvgLabel

logger = logging.getLogger(__name__)


class DeletedConversationItemsMarker(QWidget):
    """
    Shown when earlier conversation items have been deleted.
    """

    TOP_MARGIN = 28
    BOTTOM_MARGIN = 4  # Add some spacing at the bottom between other widgets during scroll

    def __init__(self) -> None:
        super().__init__()

        self.hide()

        self.setObjectName("DeletedConversationItemsMarker")

        left_tear = SvgLabel("tear-left.svg", svg_size=QSize(196, 15))
        left_tear.setMinimumWidth(196)
        left_tear.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        deletion_message = QLabel(_("Earlier files and messages deleted."))
        deletion_message.setSizePolicy(QSizePolicy.Minimum, QSizePolicy.Fixed)
        deletion_message.setWordWrap(False)
        deletion_message.setObjectName("DeletedConversationItemsMessage")

        right_tear = SvgLabel("tear-right.svg", svg_size=QSize(196, 15))
        right_tear.setMinimumWidth(196)
        right_tear.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        layout = QGridLayout()
        layout.setContentsMargins(0, self.TOP_MARGIN, 0, self.BOTTOM_MARGIN)

        layout.addWidget(left_tear, 0, 0, Qt.AlignRight)
        layout.addWidget(deletion_message, 0, 1, Qt.AlignCenter)
        layout.addWidget(right_tear, 0, 2, Qt.AlignLeft)

        layout.setColumnStretch(0, 1)
        layout.setColumnStretch(1, 0)
        layout.setColumnStretch(2, 1)

        self.setLayout(layout)
