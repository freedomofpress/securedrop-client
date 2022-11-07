# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright © 2022 The Freedom of the Press Foundation.
"""
Stores and provides read/write access to the internal state of the SecureDrop Client.

Note: the Graphical User Interface MUST NOT write state, except in QActions.
"""
from typing import Dict, List, Optional

from PyQt5.QtCore import QObject, pyqtSignal, pyqtSlot

from securedrop_client.database import Database

from .domain import ConversationId, File, FileId, SourceId


class State(QObject):
    """Stores and provides read/write access to the internal state of the SecureDrop Client.

    Note: the Graphical User Interface SHOULD NOT write state, except in QActions.
    """

    selected_conversation_files_changed = pyqtSignal()

    def __init__(self, database: Optional[Database] = None) -> None:
        super().__init__()
        self._files: Dict[FileId, File] = {}
        self._conversation_files: Dict[ConversationId, List[File]] = {}
        self._selected_conversation: Optional[ConversationId] = None

        if database is not None:
            self._initialize_from_database(database)

    def _initialize_from_database(self, database: Database) -> None:
        persisted_files = database.get_files()
        for persisted_file in persisted_files:
            conversation_id = ConversationId(persisted_file.source.uuid)
            file_id = FileId(persisted_file.uuid)
            self.add_file(conversation_id, file_id)
            if persisted_file.is_downloaded:
                known_file = self.file(file_id)
                if known_file is not None:
                    known_file.is_downloaded = True

    def add_file(self, cid: ConversationId, fid: FileId) -> None:
        file = File(fid)  # store references to the same object
        if fid not in self._files.keys():
            self._files[fid] = file

        if cid not in self._conversation_files.keys():
            self._conversation_files[cid] = []

        file_is_known = False
        for known_file in self._conversation_files[cid]:
            if fid == known_file.id:
                file_is_known = True
        if not file_is_known:
            self._conversation_files[cid].append(file)
            if cid == self._selected_conversation:
                self.selected_conversation_files_changed.emit()

    def remove_conversation_files(self, id: ConversationId) -> None:
        self._conversation_files[id] = []
        if id == self._selected_conversation:
            self.selected_conversation_files_changed.emit()

    def conversation_files(self, id: ConversationId) -> List[File]:
        default: List[File] = []
        return self._conversation_files.get(id, default)

    def file(self, id: FileId) -> Optional[File]:
        return self._files.get(id, None)

    def record_file_download(self, id: FileId) -> None:
        if id not in self._files.keys():
            pass
        else:
            self._files[id].is_downloaded = True
            self.selected_conversation_files_changed.emit()

    @property
    def selected_conversation(self) -> Optional[ConversationId]:
        """The identifier of the currently selected conversation, or None"""
        return self._selected_conversation

    @selected_conversation.setter
    def selected_conversation(self, id: Optional[ConversationId]) -> None:
        self._selected_conversation = id
        self.selected_conversation_files_changed.emit()

    @property
    def selected_conversation_has_downloadable_files(self) -> bool:
        """Whether the selected conversation has any files that are not already downloaded"""
        selected_conversation_id = self._selected_conversation
        if selected_conversation_id is None:
            return False

        default: List[File] = []
        for f in self._conversation_files.get(selected_conversation_id, default):
            if not f.is_downloaded:
                return True
        return False

    @pyqtSlot(SourceId)
    def set_selected_conversation_for_source(self, source_id: SourceId) -> None:
        self.selected_conversation = ConversationId(str(source_id))

    @pyqtSlot()
    def clear_selected_conversation(self) -> None:
        self.selected_conversation = None
