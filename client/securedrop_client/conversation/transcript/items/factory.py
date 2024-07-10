from typing import Optional

from securedrop_client import db as database

from .file import File
from .item import Item
from .message import Message


def transcribe(record: database.Base) -> Optional[Item]:
    if isinstance(record, database.Message) or isinstance(record, database.Reply):
        return Message(record)
    if isinstance(record, database.File):
        return File(record)
    else:
        return None
