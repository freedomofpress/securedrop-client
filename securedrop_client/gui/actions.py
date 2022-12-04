"""
The actions available to the journalist.

Over time, this module could become the interface between
the GUI and the controller.
"""
import logging
from gettext import gettext as _
from pathlib import Path
from typing import Callable, Optional

from PyQt5.QtCore import Qt, pyqtSignal, pyqtSlot
from PyQt5.QtWidgets import QAction, QDialog, QMenu

from securedrop_client import conversation, export, state
from securedrop_client.db import Source
from securedrop_client.logic import Controller
from securedrop_client.utils import safe_mkdir

logger = logging.getLogger(__name__)


class DownloadConversation(QAction):
    """Download all files and messages of the currently selected conversation."""

    def __init__(
        self, parent: QMenu, controller: Controller, app_state: Optional[state.State] = None
    ) -> None:
        self._controller = controller
        self._state = app_state
        self._text = _("Download All Files")
        super().__init__(self._text, parent)
        self.setShortcut(Qt.CTRL + Qt.Key_D)
        self.triggered.connect(self.on_triggered)
        self.setShortcutVisibleInContextMenu(True)

        self._connect_enabled_to_conversation_changes()
        self._set_enabled_initial_value()

    @pyqtSlot()
    def on_triggered(self) -> None:
        if self._controller.api is None:
            self._controller.on_action_requiring_login()
        else:
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


class DeleteSource(QAction):
    """Use this action to delete the source record."""

    def __init__(
        self,
        source: Source,
        parent: QMenu,
        controller: Controller,
        confirmation_dialog: Callable[[Source], QDialog],
    ) -> None:
        self.source = source
        self.controller = controller
        self.text = _("Delete Source Account")

        super().__init__(self.text, parent)

        self._confirmation_dialog = confirmation_dialog(self.source)
        self._confirmation_dialog.accepted.connect(
            lambda: self.controller.delete_source(self.source)
        )
        self.triggered.connect(self.trigger)

    def trigger(self) -> None:
        if self.controller.api is None:
            self.controller.on_action_requiring_login()
        else:
            self._confirmation_dialog.exec()


class DeleteConversation(QAction):
    """Use this action to delete a source's submissions and replies."""

    def __init__(
        self,
        source: Source,
        parent: QMenu,
        controller: Controller,
        confirmation_dialog: Callable[[Source], QDialog],
        app_state: Optional[state.State] = None,
    ) -> None:
        self.source = source
        self.controller = controller
        self._state = app_state
        self.text = _("Delete All Files and Messages")

        super().__init__(self.text, parent)

        self._confirmation_dialog = confirmation_dialog(self.source)
        self._confirmation_dialog.accepted.connect(lambda: self._on_confirmation_dialog_accepted())
        self.triggered.connect(self.trigger)

    def trigger(self) -> None:
        if self.controller.api is None:
            self.controller.on_action_requiring_login()
        else:
            self._confirmation_dialog.exec()

    def _on_confirmation_dialog_accepted(self) -> None:
        if self._state is not None:
            id = self._state.selected_conversation
            if id is None:
                return
            self.controller.delete_conversation(self.source)
            self._state.remove_conversation_files(id)


class PrintConversation(QAction):
    """Use this action to print a transcript of the messages, replies, etc.

    The transcript includes references to any attached files.
    """

    printer_job_enqueued = pyqtSignal(list)

    def __init__(
        self,
        source: Source,
        parent: QMenu,
        controller: Controller,
        confirmation_dialog: Callable[[export.Printer, str], QDialog],
        error_dialog: Callable[[str, str], QDialog],
    ) -> None:
        title = _("Print Conversation")
        super().__init__(title, parent)

        self._controller = controller
        self._source = source
        printing_service = export.getService()
        self._printer = export.getPrinter(printing_service)
        self._create_error_dialog = error_dialog
        self._create_confirmation_dialog = confirmation_dialog
        self._printing_job_id = self._source.journalist_designation
        self._printing_job_failure_notification_in_progress = False

        self.setShortcut(Qt.CTRL + Qt.Key_P)

        self._printer.job_failed.connect(self._on_printing_job_failed)
        self._printer.job_done.connect(self._on_printing_job_done)
        self.triggered.connect(self.trigger)

        self._printer.enqueue_job_on(self.printer_job_enqueued)

    @pyqtSlot()
    def trigger(self) -> None:
        if self._controller.api is None:
            self._controller.on_action_requiring_login()
        else:
            self._printer.connect()
            self._confirmation_dialog = self._create_confirmation_dialog(
                self._printer, self._transcript_display_name
            )
            self._confirmation_dialog.accepted.connect(self._on_confirmation_dialog_accepted)
            self._confirmation_dialog.rejected.connect(self._on_confirmation_dialog_rejected)
            self._confirmation_dialog.finished.connect(self._printer.disconnect)
            self._confirmation_dialog.show()

    @pyqtSlot()
    def _on_confirmation_dialog_rejected(self) -> None:
        self.setEnabled(True)
        self._confirmation_dialog.deleteLater()

    @pyqtSlot()
    def _on_confirmation_dialog_accepted(self) -> None:
        self.setEnabled(False)
        self._enqueue_printing_job(self._transcript_path)
        self._confirmation_dialog.deleteLater()

    @pyqtSlot(str)
    def _on_printing_job_done(self, job_id: str) -> None:
        self.setEnabled(True)

    @pyqtSlot(str, str)
    def _on_printing_job_failed(self, job_id: str, reason: str) -> None:
        self._error_dialog = self._create_error_dialog(job_id, reason)
        self._error_dialog.finished.connect(self._on_error_dialog_finished)
        self._error_dialog.finished.connect(self._printer.disconnect)
        self._error_dialog.show()

    @pyqtSlot(int)
    def _on_error_dialog_finished(self, _result: int) -> None:
        self.setEnabled(True)
        self._error_dialog.deleteLater()

    def _start_printer(self) -> None:
        """Start the printer in a thread-safe manner."""
        self.printer_start_requested.emit()

    def _enqueue_printing_job(self, file_path: Path) -> None:
        """Enqueue a printing job in a thread-safe manner."""

        transcript = conversation.Transcript(self._source)
        safe_mkdir(file_path.parent)

        with open(file_path, "w") as f:
            f.write(str(transcript))
            self.printer_job_enqueued.emit([str(file_path)])

    @property
    def _transcript_path(self) -> Path:
        """The transcript path. This is te source of truth for this data."""
        return (
            Path(self._controller.data_dir)
            .joinpath(self._source.journalist_filename)
            .joinpath("conversation.txt")
        )

    @property
    def _transcript_display_name(self) -> str:
        """The transcript name for display purposes.

        Example: wonderful_source/conversation.txt
        """
        return str(self._transcript_path.relative_to(self._transcript_path.parents[1]))
