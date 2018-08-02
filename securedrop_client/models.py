import os
import sqlite3
import subprocess

from sqlalchemy import Column, create_engine, Integer, String
from sqlalchemy.ext.declarative import declarative_base


# TODO: Store this in config file, see issue #2
DB_PATH = os.path.abspath('svs.sqlite')

if not os.path.exists(DB_PATH):
    sqlite3.connect(DB_PATH)
    subprocess.check_output('alembic upgrade head'.split())

engine = create_engine('sqlite:///{}'.format(DB_PATH))
Base = declarative_base()


class User(Base):
    __tablename__ = 'users'
    id = Column(Integer, primary_key=True)
    username = Column(String(255), nullable=False, unique=True)

    def __init__(self, username):
        self.username = username

    def __repr__(self):
        return "<Journalist: {}".format(self.username)
