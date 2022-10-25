from typing import Optional


class Item:
    @property
    def transcript(self) -> str:
        """A transcription of the conversation item."""
        raise NotImplementedError  # pragma: nocover

    @property
    def context(self) -> Optional[str]:
        """Some context about the conversation item."""
        raise NotImplementedError  # pragma: nocover
