import datetime
import os
from enum import Enum
from pathlib import Path
from typing import Any, Dict, List, Union  # noqa: F401
from uuid import uuid4

from sqlalchemy import (
    Boolean,
    CheckConstraint,
    Column,
    DateTime,
    ForeignKey,
    Integer,
    MetaData,
    String,
    Text,
    UniqueConstraint,
    create_engine,
    text,
)
from sqlalchemy.ext.declarative import declarative_base
from sqlalchemy.orm import backref, relationship, scoped_session, sessionmaker

convention = {
    "ix": "ix_%(column_0_label)s",
    "uq": "uq_%(table_name)s_%(column_0_name)s",
    "ck": "ck_%(table_name)s_%(column_0_name)s",
    "fk": "fk_%(table_name)s_%(column_0_name)s_%(referred_table_name)s",
    "pk": "pk_%(table_name)s",
}

metadata = MetaData(naming_convention=convention)

Base = declarative_base(metadata=metadata)  # type: Any


def make_session_maker(home: str) -> scoped_session:
    db_path = os.path.join(home, "svs.sqlite")
    engine = create_engine("sqlite:///{}".format(db_path))
    if os.path.exists(db_path) and oct(os.stat(db_path).st_mode) != "0o100600":
        os.chmod(db_path, 0o600)
    maker = sessionmaker(bind=engine)
    return scoped_session(maker)


class User(Base):

    __tablename__ = "users"

    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    username = Column(String(255), nullable=False)
    firstname = Column(String(64))
    lastname = Column(String(64))

    def __repr__(self) -> str:
        return "<Journalist {}: {}>".format(self.uuid, self.username)

    @property
    def deleted(self) -> bool:
        return self.username == "deleted"

    @property
    def fullname(self) -> str:
        if self.deleted:
            return ""
        if self.firstname and self.lastname:
            return self.firstname + " " + self.lastname
        elif self.firstname:
            return self.firstname
        elif self.lastname:
            return self.lastname
        else:
            return self.username

    @property
    def initials(self) -> str:
        if self.deleted:
            return ""
        if self.firstname and self.lastname:
            return self.firstname[0].lower() + self.lastname[0].lower()
        elif self.firstname and len(self.firstname) >= 2:
            return self.firstname[0:2].lower()
        elif self.lastname and len(self.lastname) >= 2:
            return self.lastname[0:2].lower()
        else:
            return self.username[0:2].lower()  # username must be at least 3 characters


class DeletedUser(User):
    def __init__(self) -> None:
        super().__init__(uuid=str(uuid4()), username="deleted")


class Source(Base):

    __tablename__ = "sources"

    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    journalist_designation = Column(String(255), nullable=False)
    document_count = Column(Integer, server_default=text("0"), nullable=False)
    is_flagged = Column(Boolean(name="is_flagged"), server_default=text("0"))
    public_key = Column(Text, nullable=True)
    fingerprint = Column(String(64))
    interaction_count = Column(Integer, server_default=text("0"), nullable=False)
    is_starred = Column(Boolean(name="is_starred"), server_default=text("0"))
    last_updated = Column(DateTime)

    def __repr__(self) -> str:
        return "<Source {}: {}>".format(self.uuid, self.journalist_designation)

    @property
    def collection(self) -> List:
        """Return the list of submissions, replies, messages, and drafts for this
        source, sorted in ascending order by the filename/interaction count."""
        collection = []  # type: List
        collection.extend(self.messages)
        collection.extend(self.files)
        collection.extend(self.replies)
        collection.extend(self.draftreplies)
        # Push pending replies to the end of the collection, then sort by
        # file_counter, then by timestamp (the latter used only for draft replies).
        collection.sort(
            key=lambda x: (
                getattr(x, "is_pending", False),
                x.file_counter,
                getattr(x, "timestamp", datetime.datetime(datetime.MINYEAR, 1, 1)),
            )
        )
        return collection

    @property
    def server_collection(self) -> List:
        """Return the list of submissions, replies, and messages for this source.
        These are the items that have been either successfully sent to the server,
        or they have been retrieved from the server."""
        collection = []  # type: List
        collection.extend(self.messages)
        collection.extend(self.files)
        collection.extend(self.replies)
        collection.sort(key=lambda x: x.file_counter)
        return collection

    @property
    def journalist_filename(self) -> str:
        valid_chars = "abcdefghijklmnopqrstuvwxyz1234567890-_"
        return "".join(
            [c for c in self.journalist_designation.lower().replace(" ", "_") if c in valid_chars]
        )

    @property
    def seen(self) -> bool:
        for item in self.collection:
            if not item.seen:
                return False

        return True


class DeletedConversation(Base):
    """
    Table that stores only source UUIDs for conversations (files and messages) that
    have been deleted locally, to prevent them from being re-added to the Messages and
    Replies tables during a 'stale sync' (network race condition).
    """

    __tablename__ = "deletedconversation"

    uuid = Column(String(36), primary_key=True, nullable=False)

    def __repr__(self) -> str:
        return "DeletedConversation (source {})".format(self.uuid)

    def __init__(self, **kwargs: Any) -> None:
        if "uuid" not in kwargs:
            raise TypeError("Keyword argument 'uuid' (source UUID) required")
        super().__init__(**kwargs)


class DeletedSource(Base):
    """
    Table that temporarily stores UUIDs of sources whose accounts are deleted
    locally, to prevent them from being re-added to the Sources table
    during a 'stale sync' (network race condition).
    """

    __tablename__ = "deletedsource"

    uuid = Column(String(36), primary_key=True, nullable=False)

    def __repr__(self) -> str:
        return "DeletedSource ({})".format(self.uuid)

    def __init__(self, **kwargs: Any) -> None:
        if "uuid" not in kwargs:
            raise TypeError("Keyword argument 'uuid' is required")
        super().__init__(**kwargs)


class Message(Base):

    __tablename__ = "messages"
    __table_args__ = (
        UniqueConstraint("source_id", "file_counter", name="uq_messages_source_id_file_counter"),
    )

    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    filename = Column(String(255), nullable=False)
    file_counter = Column(Integer, nullable=False)
    size = Column(Integer, nullable=False)
    download_url = Column(String(255), nullable=False)

    # This is whether the submission has been downloaded in the local database.
    is_downloaded = Column(Boolean(name="is_downloaded"), nullable=False, server_default=text("0"))

    # This tracks if the file had been successfully decrypted after download.
    is_decrypted = Column(
        Boolean(name="is_decrypted"),
        CheckConstraint(
            "CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END",
            name="messages_compare_is_downloaded_vs_is_decrypted",
        ),
        nullable=True,
    )

    download_error_id = Column(Integer, ForeignKey("downloaderrors.id"))
    download_error = relationship("DownloadError")

    # This reflects read status stored on the server.
    is_read = Column(Boolean(name="is_read"), nullable=False, server_default=text("0"))

    content = Column(
        Text,
        # this check constraint ensures the state of the DB is what one would expect
        CheckConstraint(
            "CASE WHEN is_downloaded = 0 THEN content IS NULL ELSE 1 END",
            name="ck_message_compare_download_vs_content",
        ),
    )

    source_id = Column(Integer, ForeignKey("sources.id"), nullable=False)
    source = relationship(
        "Source", backref=backref("messages", order_by=id, cascade="delete"), lazy="joined"
    )

    last_updated = Column(
        DateTime,
        nullable=False,
        default=datetime.datetime.utcnow,
        onupdate=datetime.datetime.utcnow,
    )

    def __init__(self, **kwargs: Any) -> None:
        if "file_counter" in kwargs:
            raise TypeError("Cannot manually set file_counter")
        filename = kwargs["filename"]
        kwargs["file_counter"] = int(filename.split("-")[0])
        super().__init__(**kwargs)

    def __str__(self) -> str:
        """
        Return something that's a useful string representation of the message.
        """
        if self.content is not None:
            return self.content
        else:
            if self.download_error is not None:
                return self.download_error.explain(self.__class__.__name__)
            return "<Message not yet available>"

    def __repr__(self) -> str:
        return "<Message {}: {}>".format(self.uuid, self.filename)

    def location(self, data_dir: str) -> str:
        """
        Return the full path to the Message's file.
        """
        return str(
            Path(data_dir)
            .joinpath(
                Path(self.source.journalist_filename, Path(self.filename).with_suffix(".txt"))
            )
            .resolve()
        )

    @property
    def seen(self) -> bool:
        """
        If the message has seen by any journalist, then the message is considered seen.

        The `is_read` boolean is used in order to recognize messages that have been downloaded
        before SecureDrop 1.6.0 (before the seen-by feature).
        """
        if self.seen_messages.count() or self.is_read:
            return True

        return False

    def seen_by(self, journalist_id: int) -> bool:
        for seen_message in self.seen_messages:
            if seen_message.journalist_id == journalist_id:
                return True

        return False

    @property
    def seen_by_list(self) -> Dict[str, User]:
        """
        For each message retrieve a dictionary of users who have seen it.
        Each dictionary item consists of the user's username as its key and the user
        object as its value.
        """
        usernames = {}  # type: Dict[str, User]
        for seen_message in self.seen_messages:
            if seen_message.journalist:
                usernames[seen_message.journalist.username] = seen_message.journalist
        return usernames


class File(Base):

    __tablename__ = "files"
    __table_args__ = (
        UniqueConstraint("source_id", "file_counter", name="uq_messages_source_id_file_counter"),
    )

    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    filename = Column(String(255), nullable=False)

    file_counter = Column(Integer, nullable=False)
    size = Column(Integer, nullable=False)
    download_url = Column(String(255), nullable=False)

    # This is whether the submission has been downloaded in the local database.
    is_downloaded = Column(Boolean(name="is_downloaded"), nullable=False, server_default=text("0"))

    # This tracks if the file had been successfully decrypted after download.
    is_decrypted = Column(
        Boolean(name="is_decrypted"),
        CheckConstraint(
            "CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END",
            name="files_compare_is_downloaded_vs_is_decrypted",
        ),
        nullable=True,
    )

    download_error_id = Column(Integer, ForeignKey("downloaderrors.id"))
    download_error = relationship("DownloadError")

    # This reflects read status stored on the server.
    is_read = Column(Boolean(name="is_read"), nullable=False, server_default=text("0"))

    source_id = Column(Integer, ForeignKey("sources.id"), nullable=False)
    source = relationship(
        "Source", backref=backref("files", order_by=id, cascade="delete"), lazy="joined"
    )

    last_updated = Column(
        DateTime,
        nullable=False,
        default=datetime.datetime.utcnow,
        onupdate=datetime.datetime.utcnow,
    )

    def __init__(self, **kwargs: Any) -> None:
        if "file_counter" in kwargs:
            raise TypeError("Cannot manually set file_counter")
        filename = kwargs["filename"]
        kwargs["file_counter"] = int(filename.split("-")[0])
        super().__init__(**kwargs)

    def __str__(self) -> str:
        """
        Return something that's a useful string representation of the file.
        """
        if self.is_downloaded:
            if self.download_error is not None:
                return self.download_error.explain(self.__class__.__name__)
            return "File: {}".format(self.filename)
        else:
            return "<Encrypted file on server>"

    def __repr__(self) -> str:
        return "<File {}>".format(self.uuid)

    def location(self, data_dir: str) -> str:
        """
        Return the full path to the File's file.
        """
        return str(
            Path(data_dir)
            .joinpath(
                Path(
                    self.source.journalist_filename,
                    "{}-{}-doc".format(self.file_counter, self.source.journalist_filename),
                    self.filename,
                )
            )
            .resolve()
        )

    @property
    def seen(self) -> bool:
        """
        If the file has been seen by any journalist, then the file is considered seen.

        The `is_read` boolean is used in order to recognize files that have been downloaded before
        SecureDrop 1.6.0 (before the seen-by feature).
        """
        if self.seen_files.count() or self.is_read:
            return True

        return False

    def seen_by(self, journalist_id: int) -> bool:
        for seen_file in self.seen_files:
            if seen_file.journalist_id == journalist_id:
                return True

        return False


class Reply(Base):

    __tablename__ = "replies"
    __table_args__ = (
        UniqueConstraint("source_id", "file_counter", name="uq_messages_source_id_file_counter"),
    )

    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    source_id = Column(Integer, ForeignKey("sources.id"), nullable=False)
    source = relationship(
        "Source", backref=backref("replies", order_by=id, cascade="delete"), lazy="joined"
    )

    journalist_id = Column(Integer, ForeignKey("users.id"))
    journalist = relationship("User", backref=backref("replies", order_by=id))

    filename = Column(String(255), nullable=False)
    file_counter = Column(Integer, nullable=False)
    size = Column(Integer)

    # This is whether the reply has been downloaded in the local database.
    is_downloaded = Column(Boolean(name="is_downloaded"), default=False)

    content = Column(
        Text,
        CheckConstraint(
            "CASE WHEN is_downloaded = 0 THEN content IS NULL ELSE 1 END",
            name="replies_compare_download_vs_content",
        ),
    )

    # This tracks if the file had been successfully decrypted after download.
    is_decrypted = Column(
        Boolean(name="is_decrypted"),
        CheckConstraint(
            "CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END",
            name="replies_compare_is_downloaded_vs_is_decrypted",
        ),
        nullable=True,
    )

    download_error_id = Column(Integer, ForeignKey("downloaderrors.id"))
    download_error = relationship("DownloadError")

    last_updated = Column(
        DateTime,
        nullable=False,
        default=datetime.datetime.utcnow,
        onupdate=datetime.datetime.utcnow,
    )

    def __init__(self, **kwargs: Any) -> None:
        if "file_counter" in kwargs:
            raise TypeError("Cannot manually set file_counter")
        filename = kwargs["filename"]
        kwargs["file_counter"] = int(filename.split("-")[0])
        super().__init__(**kwargs)

    def __str__(self) -> str:
        """
        Return something that's a useful string representation of the reply.
        """
        if self.content is not None:
            return self.content
        else:
            if self.download_error is not None:
                return self.download_error.explain(self.__class__.__name__)
            return "<Reply not yet available>"

    def __repr__(self) -> str:
        return "<Reply {}: {}>".format(self.uuid, self.filename)

    def location(self, data_dir: str) -> str:
        """
        Return the full path to the Reply's file.
        """
        return str(
            Path(data_dir)
            .joinpath(
                Path(self.source.journalist_filename, Path(self.filename).with_suffix(".txt"))
            )
            .resolve()
        )

    @property
    def seen(self) -> bool:
        """
        A reply is always seen in a global inbox.
        """
        return True

    def seen_by(self, journalist_id: int) -> bool:
        for seen_reply in self.seen_replies:
            if seen_reply.journalist_id == journalist_id:
                return True

        return False

    @property
    def seen_by_list(self) -> Dict[str, User]:
        """
        For each reply retrieve a dictionary of users who have seen it.
        Each dictionary item consists of the user's username as its key and the user
        object as its value.
        """
        usernames = {}  # type: Dict[str, User]
        for seen_reply in self.seen_replies:
            if seen_reply.journalist:
                usernames[seen_reply.journalist.username] = seen_reply.journalist
        return usernames


class DownloadErrorCodes(Enum):
    """
    Enumerated download failure modes, with templates as values.

    The templates are intended to be formatted with the class name of
    a downloadable item.
    """

    CHECKSUM_ERROR = "cannot download {object_type}"
    DECRYPTION_ERROR = "cannot decrypt {object_type}"


class DownloadError(Base):
    """
    Table of errors that can occur with downloadable items: File, Message, Reply.
    """

    __tablename__ = "downloaderrors"

    id = Column(Integer, primary_key=True)
    name = Column(String(36), unique=True, nullable=False)

    def __init__(self, name: str) -> None:
        super().__init__()
        self.name = name

    def __repr__(self) -> str:
        return "<Download error {}>".format(self.name)

    def explain(self, classname: str) -> str:
        """
        Formats the explanation type with the supplied class name.
        """
        return DownloadErrorCodes[self.name].value.format(object_type=classname.lower())


class DraftReply(Base):

    __tablename__ = "draftreplies"

    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    timestamp = Column(DateTime, nullable=False)
    source_id = Column(Integer, ForeignKey("sources.id"), nullable=False)
    source = relationship(
        "Source", backref=backref("draftreplies", order_by=id, cascade="delete"), lazy="joined"
    )
    journalist_id = Column(Integer, ForeignKey("users.id"))
    journalist = relationship("User", backref=backref("draftreplies", order_by=id))

    # Tracks where in this conversation the draft reply was sent.
    # This points to the file_counter of the previous conversation item.
    file_counter = Column(Integer, nullable=False)
    content = Column(Text)

    # This tracks the sending status of the reply.
    send_status_id = Column(Integer, ForeignKey("replysendstatuses.id"))
    send_status = relationship("ReplySendStatus")

    def __init__(self, **kwargs: Any) -> None:
        super().__init__(**kwargs)

    def __str__(self) -> str:
        """
        Return something that's a useful string representation of the reply.
        """
        if self.content is not None:
            return self.content
        else:
            return "<Reply not yet available>"

    def __repr__(self) -> str:
        return "<DraftReply {}>".format(self.uuid)

    @property
    def is_pending(self) -> bool:
        """
        True if Draft Reply is in Pending state.
        """
        return (
            self.send_status is not None
            and self.send_status.name == ReplySendStatusCodes.PENDING.value
        )

    @property
    def seen(self) -> bool:
        """
        A draft reply is always seen in a global inbox.
        """
        return True

    def seen_by(self, journalist_id: int) -> bool:
        """
        A draft reply is considered seen by everyone (we don't track who sees draft replies).
        """
        return True

    @property
    def seen_by_list(self) -> Dict[str, User]:
        """
        A draft reply is considered seen by everyone (we don't track who sees draft replies).
        Return an empty dictionary.
        """
        usernames = {}  # type: Dict[str, User]
        return usernames


class ReplySendStatus(Base):

    __tablename__ = "replysendstatuses"

    id = Column(Integer, primary_key=True)
    name = Column(String(36), unique=True, nullable=False)

    def __init__(self, name: str) -> None:
        super().__init__()
        self.name = name

    def __repr__(self) -> str:
        return "<Reply status {}>".format(self.name)


class ReplySendStatusCodes(Enum):
    """In progress (sending) replies can currently have the following statuses"""

    PENDING = "PENDING"
    FAILED = "FAILED"


class SeenFile(Base):
    __tablename__ = "seen_files"
    __table_args__ = (UniqueConstraint("file_id", "journalist_id"),)
    id = Column(Integer, primary_key=True)
    file_id = Column(Integer, ForeignKey("files.id"), nullable=False)
    journalist_id = Column(Integer, ForeignKey("users.id"), nullable=True)
    file = relationship("File", backref=backref("seen_files", lazy="dynamic", cascade="all,delete"))
    journalist = relationship("User", backref=backref("seen_files"))


class SeenMessage(Base):
    __tablename__ = "seen_messages"
    __table_args__ = (UniqueConstraint("message_id", "journalist_id"),)
    id = Column(Integer, primary_key=True)
    message_id = Column(Integer, ForeignKey("messages.id"), nullable=False)
    journalist_id = Column(Integer, ForeignKey("users.id"), nullable=True)
    message = relationship(
        "Message", backref=backref("seen_messages", lazy="dynamic", cascade="all,delete")
    )
    journalist = relationship("User", backref=backref("seen_messages"))


class SeenReply(Base):
    __tablename__ = "seen_replies"
    __table_args__ = (UniqueConstraint("reply_id", "journalist_id"),)
    id = Column(Integer, primary_key=True)
    reply_id = Column(Integer, ForeignKey("replies.id"), nullable=False)
    journalist_id = Column(Integer, ForeignKey("users.id"), nullable=True)
    reply = relationship("Reply", backref=backref("seen_replies", cascade="all,delete"))
    journalist = relationship("User", backref=backref("seen_replies"))
