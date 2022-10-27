from gettext import gettext as _
from typing import Optional

from securedrop_client import db as database

from .item import Item


class File(Item):
    def __init__(self, record: database.File):
        super().__init__()

        self.filename = record.filename
        self.sender = record.source.journalist_designation

    @property
    def context(self) -> Optional[str]:
        return _("{username} sent:\n").format(username=self.sender)

    @property
    def transcript(self) -> str:
        return _("File: {filename}\n").format(filename=self.filename)
