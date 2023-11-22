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

import html
import logging
from gettext import gettext as _

from PyQt5.QtCore import QSize, Qt
from PyQt5.QtGui import QCursor

from securedrop_client.gui.base import SvgPushButton
from securedrop_client.gui.unsorted.user_menu import UserMenu
from securedrop_client.logic import Controller

logger = logging.getLogger(__name__)


class UserButton(SvgPushButton):
    """An menu button for the journalist menu

    This button is responsible for launching the journalist menu on click.
    """

    def __init__(self) -> None:
        super().__init__("dropdown_arrow.svg", svg_size=QSize(9, 6))

        # Set css id
        self.setObjectName("UserButton")

        self.setFixedHeight(30)

        self.setLayoutDirection(Qt.RightToLeft)

        self._menu = UserMenu()
        self.setMenu(self._menu)

        # Set cursor.
        self.setCursor(QCursor(Qt.PointingHandCursor))

    def setup(self, controller: Controller) -> None:
        self._menu.setup(controller)

    def set_username(self, username: str) -> None:
        formatted_name = _("{}").format(html.escape(username))
        self.setText(formatted_name)
        if len(formatted_name) > 21:
            # The name will be truncated, so create a tooltip to display full
            # name if the mouse hovers over the widget.
            self.setToolTip(_("{}").format(html.escape(username)))
