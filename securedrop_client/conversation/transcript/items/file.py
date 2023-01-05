from securedrop_client import db as database

from .item import Item


class File(Item):
    type = "file"

    def __init__(self, record: database.File):
        super().__init__()

        self.filename = record.filename
        self.sender = record.source.journalist_designation
