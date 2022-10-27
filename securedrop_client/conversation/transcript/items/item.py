from typing import Optional


class Item:
    """
    A transcript item.

    Transcript items must define their `type` to be rendered by the transcript template.
    """

    type: Optional[str] = None

    @property
    def transcript(self) -> str:
        """A transcription of the conversation item."""
        raise NotImplementedError  # pragma: nocover

    @property
    def context(self) -> Optional[str]:
        """Some context about the conversation item."""
        raise NotImplementedError  # pragma: nocover
