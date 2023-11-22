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

from PyQt5.QtWidgets import QStatusBar

logger = logging.getLogger(__name__)


class ActivityStatusBar(QStatusBar):
    """
    A status bar for displaying messages about application activity to the user. Messages will be
    displayed for a given duration or until the message updated with a new message.
    """

    def __init__(self) -> None:
        super().__init__()

        # Set css id
        self.setObjectName("ActivityStatusBar")

        # Remove grip image at bottom right-hand corner
        self.setSizeGripEnabled(False)

    def update_message(self, message: str, duration: int) -> None:
        """
        Display a status message to the user.
        """
        self.showMessage(message, duration)
