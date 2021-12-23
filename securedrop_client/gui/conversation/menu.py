"""
The menu of actions that apply to a conversation.

Copyright (C) 2021  The Freedom of the Press Foundation.

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
from gettext import gettext as _

from PyQt5.QtGui import QFont
from PyQt5.QtWidgets import QMenu

from securedrop_client.db import Source
from securedrop_client.gui.actions import DeleteConversationAction, DeleteSourceAction
from securedrop_client.logic import Controller
from securedrop_client.resources import load_css


class SourceMenu(QMenu):
    """Renders menu having various operations.

    This menu provides below functionality via menu actions:

    1. Delete source

    Note: At present this only supports "delete" operation.
    """

    SOURCE_MENU_CSS = load_css("source_menu.css")

    def __init__(self, source: Source, controller: Controller) -> None:
        super().__init__()
        self.source = source
        self.controller = controller

        self.setStyleSheet(self.SOURCE_MENU_CSS)
        separator_font = QFont()
        separator_font.setLetterSpacing(QFont.AbsoluteSpacing, 2)
        separator_font.setBold(True)

        delete_section = self.addSection(_("DELETE"))
        delete_section.setFont(separator_font)

        self.addAction(DeleteConversationAction(self.source, self, self.controller))
        self.addAction(DeleteSourceAction(self.source, self, self.controller))
