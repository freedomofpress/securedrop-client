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

import arrow
from PyQt5.QtWidgets import QListWidgetItem

from securedrop_client.gui.unsorted.source_widget import SourceWidget

logger = logging.getLogger(__name__)


class SourceListWidgetItem(QListWidgetItem):
    def __lt__(self, other: "SourceListWidgetItem") -> bool:
        """
        Used for ordering widgets by timestamp of last interaction.
        """
        lw = self.listWidget()
        me = lw.itemWidget(self)
        them = lw.itemWidget(other)
        if me and them:
            assert isinstance(me, SourceWidget)
            assert isinstance(them, SourceWidget)
            my_ts = arrow.get(me.last_updated)
            other_ts = arrow.get(them.last_updated)
            return my_ts < other_ts
        return True
