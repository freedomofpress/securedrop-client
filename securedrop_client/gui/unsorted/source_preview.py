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

from securedrop_client.gui.base import SecureQLabel

logger = logging.getLogger(__name__)


class SourcePreview(SecureQLabel):
    PREVIEW_WIDTH_DIFFERENCE = 140

    def __init__(self) -> None:
        super().__init__()

    def adjust_preview(self, width: int) -> None:
        """
        This is a workaround to the workaround for https://bugreports.qt.io/browse/QTBUG-85498.
        Since QLabels containing text with long strings that cannot be wrapped have to have a fixed
        width in order to fit within the scroll list widget, we have to override the normal resizing
        logic.
        """
        new_width = width - self.PREVIEW_WIDTH_DIFFERENCE
        if self.width() == new_width:
            return

        self.setFixedWidth(new_width)
        self.max_length = self.width()
        self.refresh_preview_text()
