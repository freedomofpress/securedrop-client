# -*- coding: utf-8 -*-

import os
import random
import subprocess

from securedrop_client import db
from securedrop_client.db import DraftReply, Reply, User

from .utils import add_draft_reply, add_reply, add_source, add_user

random.seed("=^..^=..^=..^=")


class UpgradeTester:
    """
    Verify that upgrading to the target migration results in the replacement of uuid with id of the
    user in the replies table's journalist_id column.
    """

    NUM_USERS = 20
    NUM_SOURCES = 20
    NUM_REPLIES = 40

    def __init__(self, homedir):
        subprocess.check_call(["sqlite3", os.path.join(homedir, "svs.sqlite"), ".databases"])
        self.session = db.make_session_maker(homedir)()

    def load_data(self):
        """
        Load data that has the bug where user.uuid is stored in replies.journalist_id and
        draftreplies.journalist_id.
        """
        for _ in range(self.NUM_SOURCES):
            add_source(self.session)

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
            journalist = self.session.query(User).filter_by(id=journalist_id).one()
            source_id = random.randint(1, self.NUM_SOURCES)
            add_reply(self.session, journalist.uuid, source_id)

        # Add draft replies from randomly-selected journalists to a randomly-selected sources
        for _ in range(1, self.NUM_REPLIES):
            journalist_id = random.randint(1, self.NUM_USERS)
            journalist = self.session.query(User).filter_by(id=journalist_id).one()
            source_id = random.randint(1, self.NUM_SOURCES)
            add_draft_reply(self.session, journalist.uuid, source_id)

        self.session.commit()

    def check_upgrade(self):
        """
        Make sure each reply in the replies and draftreplies tables have the correct journalist_id
        stored for the associated journalist by making sure a User account exists with that
        journalist id.
        """
        replies = self.session.query(Reply).all()
        assert len(replies)

        for reply in replies:
            # Will fail if User does not exist
            self.session.query(User).filter_by(id=reply.journalist_id).one()

        draftreplies = self.session.query(DraftReply).all()
        assert len(draftreplies)

        for draftreply in draftreplies:
            # Will fail if User does not exist
            self.session.query(User).filter_by(id=draftreply.journalist_id).one()

        self.session.close()


class DowngradeTester:
    """
    Nothing to test since the downgrade path doesn't do anything.
    """

    def __init__(self, homedir):
        pass

    def load_data(self):
        pass

    def check_downgrade(self):
        pass
