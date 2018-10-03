import os

from sqlalchemy import (Boolean, Column, create_engine, DateTime, ForeignKey,
                        Integer, String, Text)
from sqlalchemy.ext.declarative import declarative_base
from sqlalchemy.orm import relationship, backref


# TODO: Store this in config file, see issue #2
DB_PATH = os.path.abspath('svs.sqlite')

engine = create_engine('sqlite:///{}'.format(DB_PATH))
Base = declarative_base()


class Source(Base):
    __tablename__ = 'sources'
    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    journalist_designation = Column(String(255), nullable=False)
    is_flagged = Column(Boolean, server_default="false")
    public_key = Column(Text, nullable=True)
    interaction_count = Column(Integer, server_default="0", nullable=False)
    is_starred = Column(Boolean, server_default="false")
    last_updated = Column(DateTime)

    def __init__(self, uuid, journalist_designation, is_flagged, public_key,
                 interaction_count, is_starred, last_updated):
        self.uuid = uuid
        self.journalist_designation = journalist_designation
        self.is_flagged = is_flagged
        self.public_key = public_key
        self.interaction_count = interaction_count
        self.is_starred = is_starred
        self.last_updated = last_updated

    def __repr__(self):
        return '<Source {}>'.format(self.journalist_designation)


class Submission(Base):
    __tablename__ = 'submissions'
    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    filename = Column(String(255), nullable=False)
    size = Column(Integer, nullable=False)

    # This is whether the submission has been downloaded in the local database.
    is_downloaded = Column(Boolean, default=False)

    # This reflects read status stored on the server.
    is_read = Column(Boolean, default=False)

    source_id = Column(Integer, ForeignKey('sources.id'))
    source = relationship("Source",
                          backref=backref("submissions", order_by=id,
                                          cascade="delete"))

    def __init__(self, source, uuid, size, filename):
        self.source_id = source.id
        self.uuid = uuid
        self.size = size
        self.filename = filename

    def __repr__(self):
        return '<Submission {}>'.format(self.filename)


class Reply(Base):
    __tablename__ = 'replies'
    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    source_id = Column(Integer, ForeignKey('sources.id'))
    source = relationship("Source",
                          backref=backref("replies", order_by=id,
                                          cascade="delete"))

    journalist_id = Column(Integer, ForeignKey('users.id'))
    journalist = relationship(
        "User", backref=backref('replies', order_by=id))

    filename = Column(String(255), nullable=False)
    size = Column(Integer, nullable=False)

    def __init__(self, uuid, journalist, source, filename, size):
        self.uuid = uuid
        self.journalist_id = journalist.id
        self.source_id = source.id
        self.filename = filename
        self.size = size

    def __repr__(self):
        return '<Reply {}>'.format(self.filename)


class User(Base):
    __tablename__ = 'users'
    id = Column(Integer, primary_key=True)
    username = Column(String(255), nullable=False, unique=True)

    def __init__(self, username):
        self.username = username

    def __repr__(self):
        return "<Journalist: {}>".format(self.username)


# Populate the database.
Base.metadata.create_all(engine)
