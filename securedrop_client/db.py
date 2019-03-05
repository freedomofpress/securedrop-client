import os

from sqlalchemy import Boolean, Column, create_engine, DateTime, ForeignKey, Integer, String, \
    Text, MetaData, CheckConstraint
from sqlalchemy.ext.declarative import declarative_base, AbstractConcreteBase
from sqlalchemy.orm import relationship, backref


convention = {
    "ix": 'ix_%(column_0_label)s',
    "uq": "uq_%(table_name)s_%(column_0_name)s",
    "ck": "ck_%(table_name)s_%(column_0_name)s",
    "fk": "fk_%(table_name)s_%(column_0_name)s_%(referred_table_name)s",
    "pk": "pk_%(table_name)s"
}

metadata = MetaData(naming_convention=convention)

Base = declarative_base(metadata=metadata)


def make_engine(home: str):
    db_path = os.path.join(home, 'svs.sqlite')
    return create_engine('sqlite:///{}'.format(db_path))


class Source(Base):

    __tablename__ = 'sources'

    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    journalist_designation = Column(String(255), nullable=False)
    document_count = Column(Integer, server_default="0", nullable=False)
    is_flagged = Column(Boolean(name='is_flagged'), server_default="0")
    public_key = Column(Text, nullable=True)
    fingerprint = Column(String(64))
    interaction_count = Column(Integer, server_default="0", nullable=False)
    is_starred = Column(Boolean(name='is_starred'), server_default="0")
    last_updated = Column(DateTime)

    def __init__(self, uuid, journalist_designation, is_flagged, public_key,
                 interaction_count, is_starred, last_updated, document_count):
        self.uuid = uuid
        self.journalist_designation = journalist_designation
        self.is_flagged = is_flagged
        self.public_key = public_key
        self.document_count = document_count
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
        collection.extend(self.messages)
        collection.extend(self.files)
        collection.extend(self.replies)
        collection.sort(key=lambda x: int(x.filename.split('-')[0]))
        return collection


class Submission(AbstractConcreteBase, Base):
    pass


class Message(Submission):

    __tablename__ = 'messages'
    __mapper_args__ = {
        'polymorphic_identity': 'message',
        'concrete': True,
    }

    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    filename = Column(String(255), nullable=False)
    size = Column(Integer, nullable=False)
    download_url = Column(String(255), nullable=False)

    # This is whether the submission has been downloaded in the local database.
    is_downloaded = Column(Boolean(name='is_downloaded'), nullable=False, server_default="0")

    # This reflects read status stored on the server.
    is_read = Column(Boolean(name='is_read'), nullable=False, server_default="0")

    content = Column(
        Text,
        # this check contraint ensures the state of the DB is what one would expect
        CheckConstraint('CASE WHEN is_downloaded = 0 THEN content IS NULL ELSE 1 END',
                        name='compare_download_vs_content')
    )

    source_id = Column(Integer, ForeignKey('sources.id'))
    source = relationship("Source",
                          backref=backref("messages", order_by=id,
                                          cascade="delete"))

    def __repr__(self):
        return '<Message {}>'.format(self.filename)


class File(Submission):

    __tablename__ = 'files'
    __mapper_args__ = {
        'polymorphic_identity': 'file',
        'concrete': True,
    }

    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    filename = Column(String(255), nullable=False)
    size = Column(Integer, nullable=False)
    download_url = Column(String(255), nullable=False)

    # This is whether the submission has been downloaded in the local database.
    is_downloaded = Column(Boolean(name='is_downloaded'), nullable=False, server_default="0")

    # This reflects read status stored on the server.
    is_read = Column(Boolean(name='is_read'), nullable=False, server_default="0")

    source_id = Column(Integer, ForeignKey('sources.id'))
    source = relationship("Source",
                          backref=backref("files", order_by=id,
                                          cascade="delete"))

    def __repr__(self):
        return '<File {}>'.format(self.filename)


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
    size = Column(Integer)

    # This is whether the reply has been downloaded in the local database.
    is_downloaded = Column(Boolean(name='is_downloaded'),
                           default=False)

    def __repr__(self):
        return '<Reply {}>'.format(self.filename)


class User(Base):

    __tablename__ = 'users'

    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    username = Column(String(255), nullable=False)

    def __init__(self, username):
        self.username = username

    def __repr__(self):
        return "<Journalist: {}>".format(self.username)
