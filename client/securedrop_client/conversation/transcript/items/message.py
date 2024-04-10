from securedrop_client import db as database

from .item import Item


class Message(Item):
    type = "message"

    def __init__(self, record: database.Message | database.Reply):
        super().__init__()

        self.content = record.content

        if isinstance(record, database.Message):
            self.sender = record.source.journalist_designation
        else:
            self.sender = record.journalist.username
