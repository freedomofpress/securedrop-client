"""
The actions available to the journalist.

Over time, this module could become the interface between
the GUI and the controller.
"""
from gettext import gettext as _
from typing import Optional

from PyQt5.QtCore import Qt, pyqtSlot
from PyQt5.QtWidgets import QAction, QMenu

from securedrop_client import state
from securedrop_client.db import Source
from securedrop_client.gui.conversation import DeleteConversationDialog
from securedrop_client.gui.source import DeleteSourceDialog
from securedrop_client.logic import Controller


class DownloadConversation(QAction):
    """Download all files and messages of the currently selected conversation."""

    def __init__(
        self, parent: QMenu, controller: Controller, app_state: Optional[state.State] = None
    ) -> None:
        self._controller = controller
        self._state = app_state
        self._text = _("All Files")
        super().__init__(self._text, parent)
        self.setShortcut(Qt.CTRL + Qt.Key_D)
        self.triggered.connect(self.on_triggered)
        self.setShortcutVisibleInContextMenu(True)

        self._connect_enabled_to_conversation_changes()
        self._set_enabled_initial_value()

    @pyqtSlot()
    def on_triggered(self) -> None:
        if self._state is not None:
            id = self._state.selected_conversation
            if id is None:
                return
            self._controller.download_conversation(id)

    def _connect_enabled_to_conversation_changes(self) -> None:
        if self._state is not None:
            self._state.selected_conversation_files_changed.connect(
                self._on_selected_conversation_files_changed
            )

    @pyqtSlot()
    def _on_selected_conversation_files_changed(self) -> None:
        if self._state is None:
            return
        if self._state.selected_conversation_has_downloadable_files:
            self.setEnabled(True)
        else:
            self.setEnabled(False)

    def _set_enabled_initial_value(self) -> None:
        self._on_selected_conversation_files_changed()


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
