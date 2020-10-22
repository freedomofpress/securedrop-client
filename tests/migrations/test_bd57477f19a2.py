# -*- coding: utf-8 -*-

import os
import random
import subprocess

import pytest
from sqlalchemy import text
from sqlalchemy.exc import IntegrityError

from securedrop_client import db
from securedrop_client.db import Reply, User

from .utils import (
    add_file,
    add_message,
    add_reply,
    add_source,
    add_user,
    mark_file_as_seen,
    mark_message_as_seen,
    mark_reply_as_seen,
)


class UpgradeTester:
    """
    Verify that upgrading to the target migration results in the creation of the seen tables.
    """

    NUM_USERS = 20
    NUM_SOURCES = 20
    NUM_REPLIES = 40

    def __init__(self, homedir):
        subprocess.check_call(["sqlite3", os.path.join(homedir, "svs.sqlite"), ".databases"])
        self.session = db.make_session_maker(homedir)()

    def load_data(self):
        for source_id in range(1, self.NUM_SOURCES + 1):
            add_source(self.session)

            # Add zero to a few messages from each source, some messages are set to downloaded
            for _ in range(random.randint(0, 2)):
                add_message(self.session, source_id)

            # Add zero to a few files from each source, some files are set to downloaded
            for _ in range(random.randint(0, 2)):
                add_file(self.session, source_id)

        self.session.commit()

        for i in range(self.NUM_USERS):
            if i == 0:
                # As of this migration, the server tells the client that the associated journalist
                # of a reply has been deleted by returning "deleted" as the uuid of the associated
                # journalist. This gets stored as the jouranlist_id in the replies table.
                #
                # Make sure to test this case as well.
                add_user(self.session, "deleted")
                source_id = random.randint(1, self.NUM_SOURCES)
                user = self.session.query(User).filter_by(uuid="deleted").one()
                add_reply(self.session, user.id, source_id)
            else:
                add_user(self.session)

        self.session.commit()

        # Add replies from randomly-selected journalists to a randomly-selected sources
        for _ in range(1, self.NUM_REPLIES):
            journalist_id = random.randint(1, self.NUM_USERS)
            source_id = random.randint(1, self.NUM_SOURCES)
            add_reply(self.session, journalist_id, source_id)

        self.session.commit()

    def check_upgrade(self):
        """
        Make sure seen tables exist and work as expected.
        """
        replies = self.session.query(Reply).all()
        assert len(replies)

        for reply in replies:
            # Will fail if User does not exist
            self.session.query(User).filter_by(id=reply.journalist_id).one()

        sql = "SELECT * FROM files"
        files = self.session.execute(text(sql)).fetchall()

        sql = "SELECT * FROM messages"
        messages = self.session.execute(text(sql)).fetchall()

        sql = "SELECT * FROM replies"
        replies = self.session.execute(text(sql)).fetchall()

        # Now seen tables exist, so you should be able to mark some files, messages, and replies
        # as seen
        for file in files:
            if random.choice([0, 1]):
                selected_journo_id = random.randint(1, self.NUM_USERS)
                mark_file_as_seen(self.session, file.id, selected_journo_id)
        for message in messages:
            if random.choice([0, 1]):
                selected_journo_id = random.randint(1, self.NUM_USERS)
                mark_message_as_seen(self.session, message.id, selected_journo_id)
        for reply in replies:
            if random.choice([0, 1]):
                selected_journo_id = random.randint(1, self.NUM_USERS)
                mark_reply_as_seen(self.session, reply.id, selected_journo_id)

        # Check unique constraint on (reply_id, journalist_id)
        params = {"reply_id": 100, "journalist_id": 100}
        sql = """
        INSERT INTO seen_replies (reply_id, journalist_id)
        VALUES (:reply_id, :journalist_id);
        """
        self.session.execute(text(sql), params)
        with pytest.raises(IntegrityError):
            self.session.execute(text(sql), params)

        # Check unique constraint on (message_id, journalist_id)
        params = {"message_id": 100, "journalist_id": 100}
        sql = """
        INSERT INTO seen_messages (message_id, journalist_id)
        VALUES (:message_id, :journalist_id);
        """
        self.session.execute(text(sql), params)
        with pytest.raises(IntegrityError):
            self.session.execute(text(sql), params)

        # Check unique constraint on (file_id, journalist_id)
        params = {"file_id": 101, "journalist_id": 100}
        sql = """
        INSERT INTO seen_files (file_id, journalist_id)
        VALUES (:file_id, :journalist_id);
        """
        self.session.execute(text(sql), params)
        with pytest.raises(IntegrityError):
            self.session.execute(text(sql), params)


class DowngradeTester:
    """
    Verify that downgrading from the target migration keeps in place the updates from the migration
    since there is no need to add bad data back into the db (the migration is backwards compatible).
    """

    NUM_USERS = 20
    NUM_SOURCES = 20
    NUM_REPLIES = 40

    def __init__(self, homedir):
        subprocess.check_call(["sqlite3", os.path.join(homedir, "svs.sqlite"), ".databases"])
        self.session = db.make_session_maker(homedir)()

    def load_data(self):
        for source_id in range(1, self.NUM_SOURCES + 1):
            add_source(self.session)

            # Add zero to a few messages from each source, some messages are set to downloaded
            for _ in range(random.randint(0, 3)):
                add_message(self.session, source_id)

            # Add zero to a few files from each source, some files are set to downloaded
            for _ in range(random.randint(0, 3)):
                add_file(self.session, source_id)

        self.session.commit()

        for i in range(self.NUM_USERS):
            if i == 0:
                # As of this migration, the server tells the client that the associated journalist
                # of a reply has been deleted by returning "deleted" as the uuid of the associated
                # journalist. This gets stored as the jouranlist_id in the replies table.
                #
                # Make sure to test this case as well.
                add_user(self.session, "deleted")
                source_id = random.randint(1, self.NUM_SOURCES)
                add_reply(self.session, "deleted", source_id)
            else:
                add_user(self.session)

        self.session.commit()

        # Add replies from randomly-selected journalists to a randomly-selected sources
        for _ in range(1, self.NUM_REPLIES):
            journalist_id = random.randint(1, self.NUM_USERS)
            source_id = random.randint(1, self.NUM_SOURCES)
            add_reply(self.session, journalist_id, source_id)

        self.session.commit()

        # Mark some files, messages, and replies as seen
        sql = "SELECT * FROM files"
        files = self.session.execute(text(sql)).fetchall()
        for file in files:
            if random.choice([0, 1]):
                selected_journo_id = random.randint(1, self.NUM_USERS)
                mark_file_as_seen(self.session, file.id, selected_journo_id)

        sql = "SELECT * FROM messages"
        messages = self.session.execute(text(sql)).fetchall()
        for message in messages:
            if random.choice([0, 1]):
                selected_journo_id = random.randint(1, self.NUM_USERS)
                mark_message_as_seen(self.session, message.id, selected_journo_id)

        sql = "SELECT * FROM replies"
        replies = self.session.execute(text(sql)).fetchall()
        for reply in replies:
            if random.choice([0, 1]):
                selected_journo_id = random.randint(1, self.NUM_USERS)
                mark_reply_as_seen(self.session, reply.id, selected_journo_id)

        self.session.commit()

    def check_downgrade(self):
        """
        Check that seen tables no longer exist.
        """
        params = {"table_name": "seen_files"}
        sql = "SELECT name FROM sqlite_master WHERE type='table' AND name=:table_name;"
        seen_files_exists = self.session.execute(text(sql), params).fetchall()
        assert not seen_files_exists

        params = {"table_name": "seen_messages"}
        sql = "SELECT name FROM sqlite_master WHERE type='table' AND name=:table_name;"
        seen_messages_exists = self.session.execute(text(sql), params).fetchall()
        assert not seen_messages_exists

        params = {"table_name": "seen_replies"}
        sql = "SELECT name FROM sqlite_master WHERE type='table' AND name=:table_name;"
        seen_replies_exists = self.session.execute(text(sql), params).fetchall()
        assert not seen_replies_exists
