from typing import Optional

from jinja2 import Environment, PackageLoader, select_autoescape

from securedrop_client import db as database

from .items import Item
from .items import transcribe as transcribe_item

env = Environment(
    loader=PackageLoader("securedrop_client.conversation.transcript"),
    autoescape=select_autoescape(),
    # Since our plain-text templates have literal whitespace:
    lstrip_blocks=True,
    trim_blocks=True,
)


def transcribe(record: database.Base) -> Optional[Item]:
    return transcribe_item(record)


class Transcript:
    def __init__(self, conversation: database.Source) -> None:
        self._items = list(
            filter(
                lambda record: record is not None and record.type is not None,
                [transcribe(record) for record in conversation.collection],
            )
        )
        self._template = env.get_template("transcript.txt")

    def __str__(self) -> str:
        return self._template.render(items=self._items)
