import os

from sqlalchemy import Boolean, Column, create_engine, DateTime, ForeignKey, Integer, String, \
    Text, MetaData
from sqlalchemy.ext.declarative import declarative_base
from sqlalchemy.orm import relationship, backref


convention = {
    "ix": 'ix_%(column_0_label)s',
    "uq": "uq_%(table_name)s_%(column_0_name)s",
    "ck": "ck_%(table_name)s_%(constraint_name)s",
    "fk": "fk_%(table_name)s_%(column_0_name)s_%(referred_table_name)s",
    "pk": "pk_%(table_name)s"
}

metadata = MetaData(naming_convention=convention)

Base = declarative_base(metadata=metadata)


def make_engine(home: str):
    db_path = os.path.join(home, 'svs.sqlite')
    return create_engine('sqlite:///{}'.format(db_path))


class WithContent():

    @property
    def content(self):
        if self.is_downloaded:
            fn_no_ext, _ = os.path.splitext(self.filename)
            return self.data.get(fn_no_ext)
        else:
            return None


class Source(Base):
    __tablename__ = 'sources'
    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    journalist_designation = Column(String(255), nullable=False)
    is_flagged = Column(Boolean(name='ck_sources_is_flagged'),
                        server_default="false")
    public_key = Column(Text, nullable=True)
    interaction_count = Column(Integer, server_default="0", nullable=False)
    is_starred = Column(Boolean(name='ck_sources_is_starred'),
                        server_default="false")
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

    @property
    def collection(self):
        """Return the list of submissions and replies for this source, sorted
        in ascending order by the filename/interaction count."""
        collection = []
        collection.extend(self.submissions)
        collection.extend(self.replies)
        collection.sort(key=lambda x: int(x.filename.split('-')[0]))
        return collection


class Submission(Base, WithContent):
    __tablename__ = 'submissions'
    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    filename = Column(String(255), nullable=False)
    size = Column(Integer, nullable=False)
    download_url = Column(String(255), nullable=False)

    # This is whether the submission has been downloaded in the local database.
    is_downloaded = Column(Boolean(name='ck_submissions_is_downloaded'),
                           default=False)

    # This reflects read status stored on the server.
    is_read = Column(Boolean(name='ck_submissions_is_read'),
                     default=False)

    source_id = Column(Integer, ForeignKey('sources.id'))
    source = relationship("Source",
                          backref=backref("submissions", order_by=id,
                                          cascade="delete"))

    def __init__(self, source, uuid, size, filename, download_url):
        # ORM event catching _should_ have already initialized `self.data`

        self.source_id = source.id
        self.uuid = uuid
        self.size = size
        self.filename = filename
        self.download_url = download_url
        self.is_download = False

    def __repr__(self):
        return '<Submission {}>'.format(self.filename)


class Reply(Base, WithContent):
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

    # This is whether the reply has been downloaded in the local database.
    is_downloaded = Column(Boolean(name='ck_replies_is_downloaded'),
                           default=False)

    def __init__(self, uuid, journalist, source, filename, size):
        self.uuid = uuid
        self.journalist_id = journalist.id
        self.source_id = source.id
        self.filename = filename
        self.size = size
        self.is_downloaded = False

    def __repr__(self):
        return '<Reply {}>'.format(self.filename)


class User(Base):
    __tablename__ = 'users'
    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    username = Column(String(255), nullable=False, unique=True)

    def __init__(self, username):
        self.username = username

    def __repr__(self):
        return "<Journalist: {}>".format(self.username)
