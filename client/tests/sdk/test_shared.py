import datetime
import os

import pytest

from securedrop_client.sdk.sdlocalobjects import Reply, ReplyError, Source, WrongUUIDError

NUM_REPLIES_PER_SOURCE = 2


class TestShared:
    """
    Base class for test code that is shared by the API and API proxy tests.
    Tests in this file should not be prefixed with test_; they are called
    only from subclasses.
    """

    # ---------------- AUTH VALIDATION ----------------

    def api_auth(self):
        assert isinstance(self.api.token, str)
        assert isinstance(self.api.token_expiration, datetime.datetime)
        assert isinstance(self.api.token_journalist_uuid, str)
        assert isinstance(self.api.first_name, str | None)
        assert isinstance(self.api.last_name, str | None)

    # ---------------- SOURCES ----------------

    def delete_conversation(self):
        s = self.api.get_sources()[0]

        submissions = self.api.get_submissions(s)
        assert len(submissions) > 0

        replies = self.api.get_replies_from_source(s)
        assert len(replies) > 0

        self.api.delete_conversation(s.uuid)

        submissions = self.api.get_submissions(s)
        assert len(submissions) == 0

        replies = self.api.get_replies_from_source(s)
        assert len(replies) == 0

    def delete_source(self, from_string=False):
        number_of_sources_before = len(self.api.get_sources())

        s = self.api.get_sources()[0]
        if from_string:
            assert self.api.delete_source_from_string(s.uuid)
        else:
            assert self.api.delete_source(s)

        # Now there should be one less source
        sources = self.api.get_sources()
        assert len(sources) == number_of_sources_before - 1

    def failed_single_source(self):
        with pytest.raises(WrongUUIDError):
            self.api.get_source(Source(uuid="not there"))

    def flag_source(self):
        s = self.api.get_sources()[0]
        assert self.api.flag_source(s)
        # Now we will try to get the same source again
        s2 = self.api.get_source(s)
        assert not s2.is_flagged

    def get_single_source(self, from_string=False):
        s = self.api.get_sources()[0]
        # Now we will try to get the same source again

        if from_string:
            s2 = self.api.get_source_from_string(s.uuid)
        else:
            s2 = self.api.get_source(s)

        assert s.journalist_designation == s2.journalist_designation
        assert s.uuid == s2.uuid

    def get_sources(self):
        sources = self.api.get_sources()
        for source in sources:
            # Assert expected fields are present
            assert source.journalist_designation
            assert source.uuid
            assert source.last_updated

    # ---------------- SUBMISSIONS ----------------

    def delete_submission(self, from_string=False):
        number_of_submissions_before = len(self.api.get_all_submissions())

        if from_string:
            s = self.api.get_sources()[0]
            subs = self.api.get_submissions(s)
        else:
            subs = self.api.get_all_submissions()
        assert self.api.delete_submission(subs[0])
        new_subs = self.api.get_all_submissions()
        # We now should have 1 less submission
        assert len(new_subs) == number_of_submissions_before - 1

        # Let us make sure that sub[0] is not there
        for s in new_subs:
            assert s.uuid != subs[0].uuid

    def get_submission(self, from_string=False):
        # Get a source with submissions
        source_uuid = self.api.get_all_submissions()[0].source_uuid
        s = self.api.get_source(Source(uuid=source_uuid))

        subs = self.api.get_submissions(s)
        if from_string:
            sub = self.api.get_submission_from_string(subs[0].uuid, s.uuid)
        else:
            sub = self.api.get_submission(subs[0])

        assert sub.filename == subs[0].filename

    def get_all_submissions(self):
        subs = self.api.get_all_submissions()
        for submission in subs:
            assert submission.filename

    def get_submissions(self):
        s = self.api.get_sources()[0]
        subs = self.api.get_submissions(s)
        for submission in subs:
            assert submission.filename

    def get_wrong_submissions(self):
        s = self.api.get_sources()[0]
        s.uuid = "rofl-missing"
        with pytest.raises(WrongUUIDError):
            self.api.get_submissions(s)

    # ---------------- REPLIES ----------------

    def error_unencrypted_reply(self):
        s = self.api.get_sources()[0]
        with pytest.raises(ReplyError) as err:
            self.api.reply_source(s, "hello")
        assert str(err.value) == "'bad request'"

    def delete_reply(self):
        r = self.api.get_all_replies()[0]

        number_of_replies_before = len(self.api.get_all_replies())

        assert self.api.delete_reply(r)

        # We deleted one, so there must be 1 less reply now
        assert len(self.api.get_all_replies()) == number_of_replies_before - 1

    def get_replies_from_source(self):
        s = self.api.get_sources()[0]
        replies = self.api.get_replies_from_source(s)
        assert len(replies) == NUM_REPLIES_PER_SOURCE

    def get_reply_from_source(self):
        s = self.api.get_sources()[0]
        replies = self.api.get_replies_from_source(s)
        reply = replies[0]

        r = self.api.get_reply_from_source(s, reply.uuid)

        assert reply.filename == r.filename
        assert reply.size == r.size
        assert reply.reply_url == r.reply_url
        assert reply.journalist_username == r.journalist_username

    def get_all_replies(self):
        num_sources = len(self.api.get_sources())
        replies = self.api.get_all_replies()
        assert len(replies) == NUM_REPLIES_PER_SOURCE * num_sources

    def reply_source(self):
        s = self.api.get_sources()[0]
        dirname = os.path.dirname(__file__)
        with open(os.path.join(dirname, "encrypted_msg.asc")) as fobj:
            data = fobj.read()

        reply = self.api.reply_source(s, data)
        assert isinstance(reply, Reply)
        assert reply.uuid
        assert reply.filename

    def reply_source_with_uuid(self):
        s = self.api.get_sources()[0]
        dirname = os.path.dirname(__file__)
        with open(os.path.join(dirname, "encrypted_msg.asc")) as fobj:
            data = fobj.read()

        msg_uuid = "e467868c-1fbb-4b5e-bca2-87944ea83855"
        reply = self.api.reply_source(s, data, msg_uuid)
        assert reply.uuid == msg_uuid

    # ---------------- USERS ----------------

    def get_current_user(self):
        user = self.api.get_current_user()
        assert user["is_admin"]
        assert user["username"] == "journalist"
        assert "first_name" in user
        assert "last_name" in user

    def get_users(self):
        users = self.api.get_users()
        for user in users:
            # Assert expected fields are present
            assert hasattr(user, "first_name")
            assert hasattr(user, "last_name")
            # Every user has a non-empty name and UUID
            assert user.username
            assert user.uuid
            # The API should never return these fields
            assert not hasattr(user, "last_login")
            assert not hasattr(user, "is_admin")

    # ---------------- SEEN/UNSEEN ----------------

    def seen(self):
        submissions = self.api.get_all_submissions()
        replies = self.api.get_all_replies()

        file_uuids = []
        message_uuids = []
        reply_uuids = []

        for submission in submissions:
            if submission.is_file():
                file_uuids.append(submission.uuid)
            else:
                message_uuids.append(submission.uuid)

        for reply in replies:
            reply_uuids.append(reply.uuid)

        assert self.api.seen(files=file_uuids, messages=message_uuids, replies=reply_uuids)

    # ---------------- STARRING ----------------

    def star_add_remove(self):
        s = self.api.get_sources()[0]
        assert self.api.add_star(s)
        assert self.api.remove_star(s)
        for source in self.api.get_sources():
            if source.uuid == s.uuid:
                assert not source.is_starred
