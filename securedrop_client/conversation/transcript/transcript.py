from typing import List, Optional

from securedrop_client import db as database

from .items import Item
from .items import transcribe as transcribe_item


def transcribe(record: database.Base) -> Optional[Item]:
    return transcribe_item(record)


_ENTRY_SEPARATOR = "------\n"


class Transcript:
    def __init__(self, conversation: database.Source) -> None:

        self._items = [transcribe(record) for record in conversation.collection]

    def __str__(self) -> str:
        if len(self._items) <= 0:
            return "No messages."

        entries: List[str] = []

        context: Optional[str] = None

        for item in self._items:
            if item is None:
                continue

            if context is not None and context == item.context:
                entry = item.transcript
            elif item.context is None:
                entry = item.transcript  # pragma: nocover
            else:
                entry = f"{item.context}{item.transcript}"

            entries.append(entry)

            context = item.context

        return _ENTRY_SEPARATOR.join(entries)
