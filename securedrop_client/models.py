import os
import sqlite3
import subprocess

from sqlalchemy import (Boolean, Column, create_engine, DateTime, Integer,
                        String)
from sqlalchemy.ext.declarative import declarative_base


# TODO: Store this in config file, see issue #2
DB_PATH = os.path.abspath('svs.sqlite')

if not os.path.exists(DB_PATH):
    sqlite3.connect(DB_PATH)
    subprocess.check_output('alembic upgrade head'.split())

engine = create_engine('sqlite:///{}'.format(DB_PATH))
Base = declarative_base()


class Source(Base):
    __tablename__ = 'sources'
    id = Column(Integer, primary_key=True)
    uuid = Column(String(36), unique=True, nullable=False)
    journalist_designation = Column(String(255), nullable=False)
    is_flagged = Column(Boolean, default=False)
    public_key = Column(String(10000), nullable=True)
    interaction_count = Column(Integer, default=0, nullable=False)
    is_starred = Column(Boolean, default=False)
    last_updated = Column(DateTime)

    def __init__(self, uuid, journalist_designation):
        self.uuid = uuid
        self.journalist_designation = journalist_designation


class User(Base):
    __tablename__ = 'users'
    id = Column(Integer, primary_key=True)
    username = Column(String(255), nullable=False, unique=True)

    def __init__(self, username):
        self.username = username

    def __repr__(self):
        return "<Journalist: {}".format(self.username)
