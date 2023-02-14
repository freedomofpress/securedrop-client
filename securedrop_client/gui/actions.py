"""
The actions available to the journalist.

Over time, this module could become the interface between
the GUI and the controller.
"""
from contextlib import ExitStack
from gettext import gettext as _
from pathlib import Path
from typing import Callable, Optional

from PyQt5.QtCore import Qt, pyqtSlot
from PyQt5.QtWidgets import QAction, QDialog, QMenu

from securedrop_client import state
from securedrop_client.conversation import Transcript as ConversationTranscript
from securedrop_client.db import Source
from securedrop_client.gui.conversation import ExportDevice as ConversationExportDevice
from securedrop_client.gui.conversation import ExportDialog as ExportConversationDialog
from securedrop_client.gui.conversation import (
    ExportTranscriptDialog as ExportConversationTranscriptDialog,
)
from securedrop_client.gui.conversation import (
    PrintTranscriptDialog as PrintConversationTranscriptDialog,
)
from securedrop_client.logic import Controller
from securedrop_client.utils import safe_mkdir


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


class DeleteSourceAction(QAction):
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
        text = _("Delete Source Account")

        super().__init__(text, parent)

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


class DeleteConversationAction(QAction):
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
        text = _("Delete All Files and Messages")

        super().__init__(text, parent)

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


class PrintConversationAction(QAction):  # pragma: nocover
    def __init__(
        self,
        parent: QMenu,
        controller: Controller,
        source: Source,
    ) -> None:
        """
        Allows printing of a conversation transcript.
        """
        text = _("Print Conversation Transcript")

        super().__init__(text, parent)

        self.controller = controller
        self._source = source

        self._export_device = ConversationExportDevice(controller)

        self.triggered.connect(self._on_triggered)

    @pyqtSlot()
    def _on_triggered(self) -> None:
        """
        (Re-)generates the conversation transcript and opens a confirmation dialog to print it,
        in the manner of the existing PrintDialog.
        """
        file_path = (
            Path(self.controller.data_dir)
            .joinpath(self._source.journalist_filename)
            .joinpath("conversation.txt")
        )

        transcript = ConversationTranscript(self._source)
        safe_mkdir(file_path.parent)

        with open(file_path, "w") as f:
            f.write(str(transcript))
            # Let this context lapse to ensure the file contents
            # are written to disk.

        # Open the file to prevent it from being removed while
        # the archive is being created. Once the file object goes
        # out of scope, any pending file removal will be performed
        # by the operating system.
        with open(file_path, "r") as f:
            dialog = PrintConversationTranscriptDialog(
                self._export_device, "conversation.txt", str(file_path)
            )
            dialog.exec()


class ExportConversationTranscriptAction(QAction):  # pragma: nocover
    def __init__(
        self,
        parent: QMenu,
        controller: Controller,
        source: Source,
    ) -> None:
        """
        Allows export of a conversation transcript.
        """
        text = _("Export Conversation Transcript")

        super().__init__(text, parent)

        self.controller = controller
        self._source = source

        self._export_device = ConversationExportDevice(controller)

        self.triggered.connect(self._on_triggered)

    @pyqtSlot()
    def _on_triggered(self) -> None:
        """
        (Re-)generates the conversation transcript and opens a confirmation dialog to export it,
        in the manner of the existing ExportFileDialog.
        """
        file_path = (
            Path(self.controller.data_dir)
            .joinpath(self._source.journalist_filename)
            .joinpath("conversation.txt")
        )

        transcript = ConversationTranscript(self._source)
        safe_mkdir(file_path.parent)

        with open(file_path, "w") as f:
            f.write(str(transcript))
            # Let this context lapse to ensure the file contents
            # are written to disk.

        # Open the file to prevent it from being removed while
        # the archive is being created. Once the file object goes
        # out of scope, any pending file removal will be performed
        # by the operating system.
        with open(file_path, "r") as f:
            dialog = ExportConversationTranscriptDialog(
                self._export_device, "conversation.txt", str(file_path)
            )
            dialog.exec()


class ExportConversationAction(QAction):  # pragma: nocover
    def __init__(
        self,
        parent: QMenu,
        controller: Controller,
        source: Source,
    ) -> None:
        """
        Allows export of a conversation transcript.
        """
        text = _("Export Conversation")

        super().__init__(text, parent)

        self.controller = controller
        self._source = source

        self._export_device = ConversationExportDevice(controller)

        self.triggered.connect(self._on_triggered)

    @pyqtSlot()
    def _on_triggered(self) -> None:
        """
        (Re-)generates the conversation transcript and opens a confirmation dialog to export it
        alongside all the (attached) files that are downloaded, in the manner
        of the existing ExportFileDialog.
        """
        transcript_location = (
            Path(self.controller.data_dir)
            .joinpath(self._source.journalist_filename)
            .joinpath("conversation.txt")
        )

        transcript = ConversationTranscript(self._source)
        safe_mkdir(transcript_location.parent)

        with open(transcript_location, "w") as f:
            f.write(str(transcript))
            # Let this context lapse to ensure the file contents
            # are written to disk.

        downloaded_file_locations = [
            file.location(self.controller.data_dir)
            for file in self._source.files
            if self.controller.downloaded_file_exists(file)
        ]

        file_locations = downloaded_file_locations + [transcript_location]

        # Open the files to prevent them from being removed while
        # the archive is being created. Once the file objects go
        # out of scope, any pending file removal will be performed
        # by the operating system.
        with ExitStack() as stack:
            files = [
                stack.enter_context(open(file_location, "r")) for file_location in file_locations
            ]

            file_count = len(files)
            if file_count == 1:
                summary = "conversation.txt"
            else:
                summary = _("{file_count} files").format(file_count=file_count)

            dialog = ExportConversationDialog(
                self._export_device,
                summary,
                [str(file_location) for file_location in file_locations],
            )
            dialog.exec()
