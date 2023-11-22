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

from PyQt5.QtCore import Qt
from PyQt5.QtWidgets import QHBoxLayout, QSizePolicy, QVBoxLayout, QWidget

from securedrop_client import state
from securedrop_client.db import Source
from securedrop_client.gui.datetime_helpers import format_datetime_local
from securedrop_client.gui.unsorted.last_updated_label import LastUpdatedLabel
from securedrop_client.gui.unsorted.source_menu_button import SourceMenuButton
from securedrop_client.gui.unsorted.title_label import TitleLabel
from securedrop_client.logic import Controller

logger = logging.getLogger(__name__)


class SourceProfileShortWidget(QWidget):
    """A widget for displaying short view for Source.

    It contains below information.
    1. Journalist designation
    2. A menu to perform various operations on Source.
    """

    MARGIN_LEFT = 25
    MARGIN_RIGHT = 17
    VERTICAL_MARGIN = 14

    def __init__(
        self,
        source: Source,
        controller: Controller,
        app_state: Optional[state.State],
    ) -> None:
        super().__init__()

        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        self.source = source
        self.controller = controller

        # Set layout
        layout = QVBoxLayout()
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)
        self.setLayout(layout)

        # Create header
        header = QWidget()
        header_layout = QHBoxLayout(header)
        header_layout.setContentsMargins(
            self.MARGIN_LEFT, self.VERTICAL_MARGIN, self.MARGIN_RIGHT, self.VERTICAL_MARGIN
        )
        title = TitleLabel(self.source.journalist_designation)
        self.updated = LastUpdatedLabel(_(format_datetime_local(self.source.last_updated)))
        menu = SourceMenuButton(self.source, self.controller, app_state)
        header_layout.addWidget(title, alignment=Qt.AlignLeft)
        header_layout.addStretch()
        header_layout.addWidget(self.updated, alignment=Qt.AlignRight)
        header_layout.addWidget(menu, alignment=Qt.AlignRight)

        # Create horizontal line
        horizontal_line = QWidget()
        horizontal_line.setObjectName("SourceProfileShortWidget_horizontal_line")
        horizontal_line.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        # Add widgets
        layout.addWidget(header)
        layout.addWidget(horizontal_line)

    def update_timestamp(self) -> None:
        """
        Ensure the timestamp is always kept up to date with the latest activity
        from the source.
        """
        self.updated.setText(_(format_datetime_local(self.source.last_updated)))
