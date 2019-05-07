import typing

if typing.TYPE_CHECKING:
    from typing import Dict  # noqa: F401


class BaseError(Exception):
    pass


class ReplyError(BaseError):
    "For errors on reply messages"

    def __init__(self, message: str) -> None:
        self.msg = message

    def __str__(self) -> str:
        return repr(self.msg)


class WrongUUIDError(BaseError):
    "For missing UUID, can be for source or submission"

    def __init__(self, message: str) -> None:
        self.msg = message

    def __str__(self) -> str:
        return repr(self.msg)


class AuthError(BaseError):
    "For Authentication errors"

    def __init__(self, message: str) -> None:
        self.msg = message

    def __str__(self) -> str:
        return repr(self.msg)


class AttributeError(BaseError):
    def __init__(self, message: str) -> None:
        self.msg = message

    def __str__(self) -> str:
        return repr(self.msg)


class Reply:
    """
    This class represents a reply to the source.
    """

    def __init__(self, **kwargs) -> None:  # type: ignore
        self.filename = ""  # type: str
        self.journalist_username = ""  # type: str
        self.journalist_uuid = ""  # type: str
        self.is_deleted_by_source = False  # type: bool
        self.reply_url = ""  # type: str
        self.size = 0  # type: int
        self.source_url = ""  # type: str
        self.source_uuid = ""  # type: str
        self.uuid = ""  # type: str

        if {"uuid", "filename"} == set(kwargs.keys()):
            # Then we are creating an object for fetching from the server.
            self.uuid = kwargs["uuid"]
            self.filename = kwargs["filename"]
            return

        for key in [
            "filename",
            "journalist_username",
            "journalist_uuid",
            "is_deleted_by_source",
            "reply_url",
            "size",
            "source_url",
            "uuid",
        ]:
            if key not in kwargs:
                AttributeError("Missing key {}".format(key))
            setattr(self, key, kwargs[key])

        # Now let us set source uuid
        values = self.source_url.split("/")
        self.source_uuid = values[-1]


class Submission:
    """
    This class represents a submission object in the server.
    """

    def __init__(self, **kwargs) -> None:  # type: ignore
        self.download_url = ""  # type: str
        self.filename = ""  # type: str
        self.is_read = False  # type: bool
        self.size = 0  # type: int
        self.source_url = ""  # type: str
        self.source_uuid = ""  # type: str
        self.submission_url = ""  # type: str
        self.uuid = ""  # type: str

        if ["uuid"] == list(kwargs.keys()):
            # Means we are creating an object only for fetching from server.
            self.uuid = kwargs["uuid"]
            return

        for key in [
            "download_url",
            "filename",
            "is_read",
            "size",
            "source_url",
            "submission_url",
            "uuid",
        ]:
            if key not in kwargs:
                AttributeError("Missing key {}".format(key))
            setattr(self, key, kwargs[key])
        _, self.source_uuid = self.source_url.rsplit("/", 1)


class Source:
    """
    This class represents a source object in the server.
    """

    def __init__(self, **kwargs) -> None:  # type: ignore
        self.add_star_url = ""  # type: str
        self.interaction_count = 0  # type: int
        self.is_flagged = False  # type: bool
        self.is_starred = False  # type: bool
        self.journalist_designation = ""  # type: str
        self.key = {}  # type: Dict
        self.last_updated = ""  # type: str
        self.number_of_documents = 0  # type: int
        self.number_of_messages = 0  # type: int
        self.remove_star_url = ""  # type: str
        self.replies_url = ""  # type: str
        self.submissions_url = ""  # type: str
        self.url = ""  # type: str
        self.uuid = ""  # type: str

        if ["uuid"] == list(kwargs.keys()):
            # Means we are creating an object only for fetching from server.
            self.uuid = kwargs["uuid"]
            return

        for key in [
            "add_star_url",
            "interaction_count",
            "is_flagged",
            "is_starred",
            "journalist_designation",
            "key",
            "last_updated",
            "number_of_documents",
            "number_of_messages",
            "remove_star_url",
            "replies_url",
            "submissions_url",
            "url",
            "uuid",
        ]:
            if key not in kwargs:
                AttributeError("Missing key {}".format(key))
            setattr(self, key, kwargs[key])
