# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright © 2022 The Freedom of the Press Foundation.
"""
The types relevant to the internal state of the SecureDrop Client.
"""
from typing import NewType

ConversationId = NewType("ConversationId", str)


class SourceId(str):
    pass


class FileId(str):
    """Identifies a file without making assumptions about it.

    Once a file has been downloaded and is available locally, please use DownloadedFileId.
    """

    pass


class DownloadedFileId(str):
    """Identifies a file that is available locally."""

    def __repr__(self) -> str:
        return f"{self} (downloaded)"
