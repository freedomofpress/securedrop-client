"""
The actions available to the journalist.

Over time, this module could become the interface between
the GUI and the controller.

Copyright (C) 2021 The Freedom of the Press Foundation.

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

from PyQt5.QtWidgets import QAction, QMenu

from securedrop_client.db import Source
from securedrop_client.gui.conversation import (
    DeleteConversationDialog,  # shouldn't depend on more nested parts of the GUI
)
from securedrop_client.gui.source import (
    DeleteSourceDialog,  # shouldn't depend on more nested parts of the GUI
)
from securedrop_client.logic import Controller


class DeleteSourceAction(QAction):
    """Use this action to delete the source record."""

    def __init__(self, source: Source, parent: QMenu, controller: Controller) -> None:
        self.source = source
        self.controller = controller
        self.text = _("Entire source account")

        super().__init__(self.text, parent)

        self.confirmation_dialog = DeleteSourceDialog(self.source, self.controller)
        self.triggered.connect(self.trigger)

    def trigger(self) -> None:
        if self.controller.api is None:
            self.controller.on_action_requiring_login()
        else:
            self.confirmation_dialog.exec()


class DeleteConversationAction(QAction):
    """Use this action to delete a source's submissions and replies."""

    def __init__(self, source: Source, parent: QMenu, controller: Controller) -> None:
        self.source = source
        self.controller = controller
        self.text = _("Files and messages")

        super().__init__(self.text, parent)

        self.confirmation_dialog = DeleteConversationDialog(self.source, self.controller)
        self.triggered.connect(self.trigger)

    def trigger(self) -> None:
        if self.controller.api is None:
            self.controller.on_action_requiring_login()
        else:
            self.confirmation_dialog.exec()
