from gettext import gettext as _
from typing import Optional, Union

from securedrop_client import db as database

from .item import Item


class Message(Item):
    def __init__(self, record: Union[database.Message, database.Reply]):
        super().__init__()

        self.content = record.content

        if isinstance(record, database.Message):
            self.sender = record.source.journalist_designation
        else:
            self.sender = record.journalist.username

    @property
    def context(self) -> Optional[str]:
        return _("{username} wrote:\n").format(username=self.sender)

    @property
    def transcript(self) -> str:
        return self.content + "\n"
