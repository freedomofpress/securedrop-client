import datetime
from enum import Enum
import os

from typing import Any, List, Union  # noqa: F401

from sqlalchemy import Boolean, Column, create_engine, DateTime, ForeignKey, Integer, String, \
    Text, MetaData, CheckConstraint, text, UniqueConstraint
from sqlalchemy.ext.declarative import declarative_base
from sqlalchemy.orm import relationship, backref, scoped_session, sessionmaker


convention = {
    "ix": 'ix_%(column_0_label)s',
    "uq": "uq_%(table_name)s_%(column_0_name)s",
    "ck": "ck_%(table_name)s_%(column_0_name)s",
    "fk": "fk_%(table_name)s_%(column_0_name)s_%(referred_table_name)s",
    "pk": "pk_%(table_name)s"
}

metadata = MetaData(naming_convention=convention)

Base = declarative_base(metadata=metadata)  # type: Any


def make_session_maker(home: str) -> scoped_session:
    db_path = os.path.join(home, 'svs.sqlite')
    engine = create_engine('sqlite:///{}'.format(db_path))
    maker = sessionmaker(bind=engine)
    return scoped_session(maker)


class Source(Base):

    __tablename__ = 'sources'

    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    journalist_designation = Column(String(255), nullable=False)
    document_count = Column(Integer, server_default=text("0"), nullable=False)
    is_flagged = Column(Boolean(name='is_flagged'), server_default=text("0"))
    public_key = Column(Text, nullable=True)
    fingerprint = Column(String(64))
    interaction_count = Column(Integer, server_default=text("0"), nullable=False)
    is_starred = Column(Boolean(name='is_starred'), server_default=text("0"))
    last_updated = Column(DateTime)

    def __repr__(self) -> str:
        return '<Source {}: {}>'.format(self.uuid, self.journalist_designation)

    @property
    def collection(self) -> List:
        """Return the list of submissions, replies, messages, and drafts for this
        source, sorted in ascending order by the filename/interaction count."""
        collection = []  # type: List
        collection.extend(self.messages)
        collection.extend(self.files)
        collection.extend(self.replies)
        collection.extend(self.draftreplies)
        # Sort first by the file_counter, then by timestamp (used only for draft replies).
        collection.sort(key=lambda x: (x.file_counter,
                                       getattr(x, "timestamp",
                                               datetime.datetime(datetime.MINYEAR, 1, 1))))
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
        valid_chars = 'abcdefghijklmnopqrstuvwxyz1234567890-_'
        return ''.join([c for c in self.journalist_designation.lower().replace(
            ' ', '_') if c in valid_chars])


class Message(Base):

    __tablename__ = 'messages'
    __table_args__ = (
        UniqueConstraint('source_id', 'file_counter', name='uq_messages_source_id_file_counter'),
    )

    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    filename = Column(String(255), nullable=False)
    file_counter = Column(Integer, nullable=False)
    size = Column(Integer, nullable=False)
    download_url = Column(String(255), nullable=False)

    # This is whether the submission has been downloaded in the local database.
    is_downloaded = Column(Boolean(name='is_downloaded'), nullable=False, server_default=text("0"))

    # This tracks if the file had been successfully decrypted after download.
    is_decrypted = Column(
        Boolean(name='is_decrypted'),
        CheckConstraint('CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END',
                        name='messages_compare_is_downloaded_vs_is_decrypted'),
        nullable=True,
    )

    download_error_id = Column(
        Integer,
        ForeignKey('downloaderrors.id')
    )
    download_error = relationship("DownloadError")

    # This reflects read status stored on the server.
    is_read = Column(Boolean(name='is_read'), nullable=False, server_default=text("0"))

    content = Column(
        Text,
        # this check contraint ensures the state of the DB is what one would expect
        CheckConstraint('CASE WHEN is_downloaded = 0 THEN content IS NULL ELSE 1 END',
                        name='ck_message_compare_download_vs_content')
    )

    source_id = Column(Integer, ForeignKey('sources.id'), nullable=False)
    source = relationship("Source",
                          backref=backref("messages", order_by=id,
                                          cascade="delete"),
                          lazy="joined")

    last_updated = Column(
        DateTime,
        nullable=False,
        default=datetime.datetime.utcnow,
        onupdate=datetime.datetime.utcnow,
    )

    def __init__(self, **kwargs: Any) -> None:
        if 'file_counter' in kwargs:
            raise TypeError('Cannot manually set file_counter')
        filename = kwargs['filename']
        kwargs['file_counter'] = int(filename.split('-')[0])
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
            return '<Message not yet available>'

    def __repr__(self) -> str:
        return '<Message {}: {}>'.format(self.uuid, self.filename)

    def location(self, data_dir: str) -> str:
        '''
        Return the full path to the Message's file.
        '''
        return os.path.abspath(
            os.path.join(
                data_dir,
                self.source.journalist_filename,
                os.path.splitext(self.filename)[0] + '.txt'
            )
        )


class File(Base):

    __tablename__ = 'files'
    __table_args__ = (
        UniqueConstraint('source_id', 'file_counter', name='uq_messages_source_id_file_counter'),
    )

    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    filename = Column(String(255), nullable=False)

    file_counter = Column(Integer, nullable=False)
    size = Column(Integer, nullable=False)
    download_url = Column(String(255), nullable=False)

    # This is whether the submission has been downloaded in the local database.
    is_downloaded = Column(Boolean(name='is_downloaded'), nullable=False, server_default=text("0"))

    # This tracks if the file had been successfully decrypted after download.
    is_decrypted = Column(
        Boolean(name='is_decrypted'),
        CheckConstraint('CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END',
                        name='files_compare_is_downloaded_vs_is_decrypted'),
        nullable=True,
    )

    download_error_id = Column(
        Integer,
        ForeignKey('downloaderrors.id')
    )
    download_error = relationship("DownloadError")

    # This reflects read status stored on the server.
    is_read = Column(Boolean(name='is_read'), nullable=False, server_default=text("0"))

    source_id = Column(Integer, ForeignKey('sources.id'), nullable=False)
    source = relationship("Source",
                          backref=backref("files", order_by=id,
                                          cascade="delete"),
                          lazy="joined")

    last_updated = Column(
        DateTime,
        nullable=False,
        default=datetime.datetime.utcnow,
        onupdate=datetime.datetime.utcnow,
    )

    def __init__(self, **kwargs: Any) -> None:
        if 'file_counter' in kwargs:
            raise TypeError('Cannot manually set file_counter')
        filename = kwargs['filename']
        kwargs['file_counter'] = int(filename.split('-')[0])
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
            return '<Encrypted file on server>'

    def __repr__(self) -> str:
        return '<File {}>'.format(self.uuid)

    def location(self, data_dir: str) -> str:
        '''
        Return the full path to the File's file.
        '''
        return os.path.abspath(
            os.path.join(
                data_dir,
                self.source.journalist_filename,
                '{}-{}-doc'.format(self.file_counter, self.source.journalist_filename),
                self.filename
            )
        )


class Reply(Base):

    __tablename__ = 'replies'
    __table_args__ = (
        UniqueConstraint('source_id', 'file_counter', name='uq_messages_source_id_file_counter'),
    )

    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    source_id = Column(Integer, ForeignKey('sources.id'), nullable=False)
    source = relationship("Source",
                          backref=backref("replies", order_by=id,
                                          cascade="delete"),
                          lazy="joined")

    journalist_id = Column(Integer, ForeignKey('users.id'))
    journalist = relationship(
        "User", backref=backref('replies', order_by=id))

    filename = Column(String(255), nullable=False)
    file_counter = Column(Integer, nullable=False)
    size = Column(Integer)

    # This is whether the reply has been downloaded in the local database.
    is_downloaded = Column(Boolean(name='is_downloaded'),
                           default=False)

    content = Column(
        Text,
        CheckConstraint('CASE WHEN is_downloaded = 0 THEN content IS NULL ELSE 1 END',
                        name='replies_compare_download_vs_content')
    )

    # This tracks if the file had been successfully decrypted after download.
    is_decrypted = Column(
        Boolean(name='is_decrypted'),
        CheckConstraint('CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END',
                        name='replies_compare_is_downloaded_vs_is_decrypted'),
        nullable=True,
    )

    download_error_id = Column(
        Integer,
        ForeignKey('downloaderrors.id')
    )
    download_error = relationship("DownloadError")

    last_updated = Column(
        DateTime,
        nullable=False,
        default=datetime.datetime.utcnow,
        onupdate=datetime.datetime.utcnow,
    )

    def __init__(self, **kwargs: Any) -> None:
        if 'file_counter' in kwargs:
            raise TypeError('Cannot manually set file_counter')
        filename = kwargs['filename']
        kwargs['file_counter'] = int(filename.split('-')[0])
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
            return '<Reply not yet available>'

    def __repr__(self) -> str:
        return '<Reply {}: {}>'.format(self.uuid, self.filename)

    def location(self, data_dir: str) -> str:
        '''
        Return the full path to the Reply's file.
        '''
        return os.path.abspath(
            os.path.join(
                data_dir,
                self.source.journalist_filename,
                os.path.splitext(self.filename)[0] + '.txt'
            )
        )


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
    __tablename__ = 'downloaderrors'

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

    __tablename__ = 'draftreplies'

    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    timestamp = Column(DateTime, nullable=False)
    source_id = Column(Integer, ForeignKey('sources.id'), nullable=False)
    source = relationship("Source",
                          backref=backref("draftreplies", order_by=id,
                                          cascade="delete"),
                          lazy="joined")
    journalist_id = Column(Integer, ForeignKey('users.id'))
    journalist = relationship(
        "User", backref=backref('draftreplies', order_by=id))

    # Tracks where in this conversation the draft reply was sent.
    # This points to the file_counter of the previous conversation item.
    file_counter = Column(Integer, nullable=False)
    content = Column(Text)

    # This tracks the sending status of the reply.
    send_status_id = Column(
        Integer,
        ForeignKey('replysendstatuses.id')
    )
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
            return '<Reply not yet available>'

    def __repr__(self) -> str:
        return '<DraftReply {}>'.format(self.uuid)


class ReplySendStatus(Base):

    __tablename__ = 'replysendstatuses'

    id = Column(Integer, primary_key=True)
    name = Column(String(36), unique=True, nullable=False)

    def __init__(self, name: str) -> None:
        super().__init__()
        self.name = name

    def __repr__(self) -> str:
        return '<Reply status {}>'.format(self.name)


class ReplySendStatusCodes(Enum):
    """In progress (sending) replies can currently have the following statuses"""
    PENDING = 'PENDING'
    FAILED = 'FAILED'


class User(Base):

    __tablename__ = 'users'

    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    username = Column(String(255), nullable=False)
    firstname = Column(String(64))
    lastname = Column(String(64))

    def __repr__(self) -> str:
        return "<Journalist {}: {}>".format(self.uuid, self.username)

    @property
    def fullname(self) -> str:
        if self.firstname and self.lastname:
            return self.firstname + ' ' + self.lastname
        elif self.firstname:
            return self.firstname
        elif self.lastname:
            return self.lastname
        else:
            return self.username

    @property
    def initials(self) -> str:
        if self.firstname and self.lastname:
            return self.firstname[0].lower() + self.lastname[0].lower()
        elif self.firstname and len(self.firstname) >= 2:
            return self.firstname[0:2].lower()
        elif self.lastname and len(self.lastname) >= 2:
            return self.lastname[0:2].lower()
        else:
            return self.username[0:2].lower()  # username must be at least 3 characters
