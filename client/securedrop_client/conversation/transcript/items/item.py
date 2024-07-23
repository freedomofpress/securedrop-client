from typing import Optional


class Item:
    """
    A transcript item.

    Transcript items must define their `type` to be rendered by the transcript template.
    """

    type: Optional[str] = None
