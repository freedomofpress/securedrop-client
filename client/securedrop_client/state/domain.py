# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright © 2022‒2023 The Freedom of the Press Foundation.
"""
The types relevant to the internal state of the SecureDrop Client.
"""
from typing import NewType


class SourceId(str):
    """Identifies a source."""

    pass


ConversationId = NewType("ConversationId", str)


class FileId(str):
    """Identifies a file."""

    pass


class File:
    def __init__(self, id: FileId) -> None:
        self._id: FileId = id
        self._is_downloaded: bool = False

    @property
    def id(self) -> FileId:
        """A unique identifier file set by the server (opaque string)."""
        return self._id

    @property
    def is_downloaded(self) -> bool:
        """Whether the file is available locally."""
        return self._is_downloaded

    @is_downloaded.setter
    def is_downloaded(self, value: bool) -> None:
        self._is_downloaded = value
