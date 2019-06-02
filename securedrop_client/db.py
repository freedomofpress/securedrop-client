import os

from typing import Any, List, Union  # noqa: F401

from sqlalchemy import Boolean, Column, create_engine, DateTime, ForeignKey, Integer, String, \
    Text, MetaData, CheckConstraint, text, UniqueConstraint
from sqlalchemy.engine import Engine
from sqlalchemy.ext.declarative import declarative_base
from sqlalchemy.orm import relationship, backref, sessionmaker


SessionFactory = sessionmaker()

convention = {
    "ix": 'ix_%(column_0_label)s',
    "uq": "uq_%(table_name)s_%(column_0_name)s",
    "ck": "ck_%(table_name)s_%(column_0_name)s",
    "fk": "fk_%(table_name)s_%(column_0_name)s_%(referred_table_name)s",
    "pk": "pk_%(table_name)s"
}

metadata = MetaData(naming_convention=convention)

Base = declarative_base(metadata=metadata)  # type: Any


def make_engine(home: str) -> Engine:
    db_path = os.path.join(home, 'svs.sqlite')
    return create_engine('sqlite:///{}'.format(db_path))


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
        return '<Source {}>'.format(self.journalist_designation)

    @property
    def collection(self) -> List:
        """Return the list of submissions and replies for this source, sorted
        in ascending order by the filename/interaction count."""
        collection = []  # type: List
        collection.extend(self.messages)
        collection.extend(self.files)
        collection.extend(self.replies)
        collection.sort(key=lambda x: x.file_counter)
        return collection


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
        CheckConstraint('CASE WHEN is_decrypted = 0 THEN content IS NULL ELSE 1 END',
                        name='messages_compare_is_decrypted_vs_content'),
        nullable=True,
    )

    # This reflects read status stored on the server.
    is_read = Column(Boolean(name='is_read'), nullable=False, server_default=text("0"))

    content = Column(
        Text,
        # this check contraint ensures the state of the DB is what one would expect
        CheckConstraint('CASE WHEN is_downloaded = 0 THEN content IS NULL ELSE 1 END',
                        name='ck_message_compare_download_vs_content')
    )

    source_id = Column(Integer, ForeignKey('sources.id'), nullable=False)
    source = relationship(
        "Source", backref=backref("messages", order_by=id, lazy='subquery', cascade="delete"))

    def __init__(self, **kwargs: Any) -> None:
        if 'file_counter' in kwargs:
            raise TypeError('Cannot manually set file_counter')
        filename = kwargs['filename']
        kwargs['file_counter'] = int(filename.split('-')[0])
        super().__init__(**kwargs)

    def __repr__(self) -> str:
        return '<Message {}>'.format(self.filename)


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

    # This reflects read status stored on the server.
    is_read = Column(Boolean(name='is_read'), nullable=False, server_default=text("0"))

    source_id = Column(Integer, ForeignKey('sources.id'), nullable=False)
    source = relationship(
        "Source", backref=backref("files", order_by=id, lazy='subquery', cascade="delete"))

    def __init__(self, **kwargs: Any) -> None:
        if 'file_counter' in kwargs:
            raise TypeError('Cannot manually set file_counter')
        filename = kwargs['filename']
        kwargs['file_counter'] = int(filename.split('-')[0])
        super().__init__(**kwargs)

    def __repr__(self) -> str:
        return '<File {}>'.format(self.filename)


class Reply(Base):

    __tablename__ = 'replies'
    __table_args__ = (
        UniqueConstraint('source_id', 'file_counter', name='uq_messages_source_id_file_counter'),
    )

    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    source_id = Column(Integer, ForeignKey('sources.id'), nullable=False)
    source = relationship(
        "Source", backref=backref("replies", order_by=id, lazy='subquery', cascade="delete"))

    journalist_id = Column(Integer, ForeignKey('users.id'))
    journalist = relationship(
        "User", backref=backref('replies', order_by=id, lazy='subquery'))

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
        CheckConstraint('CASE WHEN is_decrypted = 0 THEN content IS NULL ELSE 1 END',
                        name='replies_compare_is_decrypted_vs_content'),
        nullable=True,
    )

    def __init__(self, **kwargs: Any) -> None:
        if 'file_counter' in kwargs:
            raise TypeError('Cannot manually set file_counter')
        filename = kwargs['filename']
        kwargs['file_counter'] = int(filename.split('-')[0])
        super().__init__(**kwargs)

    def __repr__(self) -> str:
        return '<Reply {}>'.format(self.filename)


class User(Base):

    __tablename__ = 'users'

    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    username = Column(String(255), nullable=False)

    def __repr__(self) -> str:
        return "<Journalist: {}>".format(self.username)
