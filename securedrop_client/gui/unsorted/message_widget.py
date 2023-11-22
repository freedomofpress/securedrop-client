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
from typing import Optional

from PyQt5.QtCore import Qt

from securedrop_client.db import User
from securedrop_client.gui.unsorted.speech_bubble import SpeechBubble

logger = logging.getLogger(__name__)


class MessageWidget(SpeechBubble):
    """
    Represents an incoming message from the source.
    """

    def __init__(  # type: ignore[no-untyped-def]
        self,
        message_uuid: str,
        message: str,
        update_signal,
        download_error_signal,
        index: int,
        container_width: int,
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

        # Setting the message bubble's layout direction left to right for the check mark
        # to appear in the required position.
        self.bubble_area.setLayoutDirection(Qt.LeftToRight)
        self.bubble_area_layout.addWidget(self.check_mark, alignment=Qt.AlignBottom)
        self.check_mark.show()
