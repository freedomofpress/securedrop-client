# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright © 2022 The Freedom of the Press Foundation.
"""
Stores and provides read/write access to the internal state of the SecureDrop Client.

Note: the Graphical User Interface MUST NOT write state, except in QActions.
"""
from typing import Dict, List, Optional

from .domain import ConversationId, File, FileId


class State:
    """Stores and provides read/write access to the internal state of the SecureDrop Client.

    Note: the Graphical User Interface SHOULD NOT write state, except in QActions.
    """

    def __init__(self) -> None:
        super().__init__()
        self._files: Dict[FileId, File] = {}
        self._conversation_files: Dict[ConversationId, List[File]] = {}
        self._selected_conversation: Optional[ConversationId] = None

    def add_file(self, cid: ConversationId, fid: FileId) -> None:
        file = File(fid)  # store references to the same object
        if fid not in self._files.keys():
            self._files[fid] = file

        if cid not in self._conversation_files.keys():
            self._conversation_files[cid] = [file]
        else:
            file_is_known = False
            for known_file in self._conversation_files[cid]:
                if fid == known_file.id:
                    file_is_known = True
            if not file_is_known:
                self._conversation_files[cid].append(file)

    def conversation_files(self, id: ConversationId) -> List[File]:
        default: List[File] = []
        return self._conversation_files.get(id, default)

    def record_file_download(self, id: FileId) -> None:
        if id not in self._files.keys():
            pass
        else:
            self._files[id].is_downloaded = True

    @property
    def selected_conversation(self) -> Optional[ConversationId]:
        """The identifier of the currently selected conversation, or None"""
        return self._selected_conversation

    @selected_conversation.setter
    def selected_conversation(self, id: Optional[ConversationId]) -> None:
        self._selected_conversation = id
