import typing

if typing.TYPE_CHECKING:
    from typing import Dict  # noqa: F401


class BaseError(Exception):
    """For generic errors not covered by other exceptions"""

    def __init__(self, message: typing.Optional[str] = None) -> None:
        self.msg = message

    def __str__(self) -> str:
        return repr(self.msg)


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
        self.journalist_uuid = ""  # type: str
        self.journalist_username = ""  # type: str
        self.journalist_first_name = ""  # type: str
        self.journalist_last_name = ""  # type: str
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
            # Fetch an object only by uuid and soure_uuid.
        elif {"uuid", "source_uuid"} == set(kwargs.keys()):
            self.uuid = kwargs["uuid"]
            self.source_uuid = kwargs["source_uuid"]
            return

        try:
            self.filename = kwargs["filename"]
            self.journalist_uuid = kwargs["journalist_uuid"]
            self.journalist_username = kwargs["journalist_username"]
            self.journalist_first_name = kwargs["journalist_first_name"]
            self.journalist_last_name = kwargs["journalist_last_name"]
            self.is_deleted_by_source = kwargs["is_deleted_by_source"]
            self.reply_url = kwargs["reply_url"]
            self.size = kwargs["size"]
            self.source_url = kwargs["source_url"]
            self.uuid = kwargs["uuid"]
            self.seen_by = kwargs["seen_by"]
        except KeyError as err:
            raise AttributeError("Missing key {}".format(err.args[0])) from err

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

        elif ["uuid", "source_uuid"] == list(kwargs.keys()):
            self.uuid = kwargs["uuid"]
            self.source_uuid = kwargs["source_uuid"]
            return

        try:
            self.download_url = kwargs["download_url"]
            self.filename = kwargs["filename"]
            self.is_read = kwargs["is_read"]
            self.size = kwargs["size"]
            self.source_url = kwargs["source_url"]
            self.submission_url = kwargs["submission_url"]
            self.uuid = kwargs["uuid"]
            self.seen_by = kwargs["seen_by"]
        except KeyError as err:
            raise AttributeError("Missing key {}".format(err.args[0])) from err

        _, self.source_uuid = self.source_url.rsplit("/", 1)

    def is_file(self) -> bool:
        return self.filename.endswith("doc.gz.gpg") or self.filename.endswith("doc.zip.gpg")


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


class User:
    """
    This class represents a user (journalist or admin) of the Journalist
    Interface.
    """

    def __init__(self, **kwargs) -> None:  # type: ignore
        self.first_name = ""  # type: str
        self.last_name = ""  # type: str
        self.username = ""  # type: str
        self.uuid = ""  # type: str

        for key in [
            "first_name",
            "last_name",
            "username",
            "uuid",
        ]:
            if key not in kwargs:
                AttributeError("Missing key {}".format(key))
            setattr(self, key, kwargs[key])
