# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright © 2022 The Freedom of the Press Foundation.
"""
Stores and provides read/write access to the internal state of the SecureDrop Client.

Note: the Graphical User Interface MUST NOT write state, except in QActions.
"""
import textwrap
from typing import Dict, List, Optional, Union

from .domain import ConversationId, DownloadedFileId, FileId, SourceId


class State:
    """Stores and provides read/write access to the internal state of the SecureDrop Client.

    Note: the Graphical User Interface SHOULD NOT write state, except in QActions.
    """

    def __init__(self) -> None:
        super().__init__()

        self._selected_conversation: Optional[ConversationId] = None
        self._conversations: Dict[ConversationId, List[Union[FileId, DownloadedFileId]]] = {}

    # read-only

    def selected_conversation(self) -> Optional[ConversationId]:
        return self._selected_conversation

    def conversation_files(self, id: ConversationId) -> List[Union[DownloadedFileId, FileId]]:
        default: List[Union[FileId, DownloadedFileId]] = []
        return self._conversations.get(id, default)

    def __repr__(self) -> str:
        return textwrap.dedent(
            f"""
                selected_conversation: {self._selected_conversation}
                conversation_files: {self._conversations}
            """
        )

    # write

    def record_file_download(self, fid: FileId) -> None:
        conversation_id: Optional[ConversationId] = None
        files: List[Union[FileId, DownloadedFileId]] = []
        # TODO: find the right data structure to access file lists by FileId or ConversationId
        for (conversation_id, files) in self._conversations.items():
            if fid in files:
                break

        i = files.index(fid)
        files.remove(fid)
        files.insert(i, DownloadedFileId(fid))
        self._conversations[conversation_id] = files

    def set_selected_conversation(self, id: Optional[SourceId]) -> None:
        if id is not None:
            self._selected_conversation = ConversationId(str(id))

    def update_or_insert_conversation(
        self, id: ConversationId, files: List[Union[FileId, DownloadedFileId]]
    ) -> None:
        known = self._conversations.get(id, [])

        # only keep known files that still exist
        kept = []
        for fid in known:
            if fid in files:
                kept.append(fid)

        new = []
        for fid in files:
            if fid not in kept:
                new.append(fid)

        # does not preserve order, though unknown files are likely newer
        kept.extend(new)
        self._conversations[id] = kept
