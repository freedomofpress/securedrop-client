import datetime
import hashlib
import os
import shutil
import tempfile
import time
import unittest

import pyotp
import pytest
import vcr
from requests.exceptions import ConnectTimeout, ReadTimeout

from sdclientapi import API, RequestTimeoutError
from sdclientapi.sdlocalobjects import (
    AuthError,
    Reply,
    ReplyError,
    Source,
    Submission,
    WrongUUIDError,
)

NUM_REPLIES_PER_SOURCE = 2


class TestAPI(unittest.TestCase):
    def setUp(self):
        self.totp = pyotp.TOTP("JHCOGO7VCER3EJ4L")
        self.username = "journalist"
        self.password = "correct horse battery staple profanity oil chewy"
        self.server = "http://127.0.0.1:8081/"

        # Because we may be using a TOTP code from a previous run that has since
        # been invalidated (or that may be invalid because of bad timing),
        # we retry repeatedly to get the token with a new TOTP code.
        #
        # It doesn't matter if these intermittent 403s are captured in the
        # cassette as we ignore them during playback.
        auth_result = None
        with vcr.use_cassette("data/test-setup.yml") as cassette:
            for i in range(3):
                totp = self.totp.now()
                self.api = API(self.server, self.username, self.password, str(totp))
                try:
                    auth_result = self.api.authenticate()
                except AuthError:
                    # Don't sleep on final retry attempt or during playback
                    if i < 2 and cassette.play_count == 0:
                        time.sleep(31)
                    continue
                # No error, let's move on
                break

        if auth_result is None:
            raise AuthError("Could not obtain API token during test setup.")

    @vcr.use_cassette("data/test-baduser.yml")
    def test_auth_baduser(self):
        self.api = API(self.server, "no", self.password, str(self.totp.now()))
        with self.assertRaises(AuthError):
            self.api.authenticate()

    @vcr.use_cassette("data/test-badpassword.yml")
    def test_auth_badpassword(self):
        self.api = API(self.server, self.username, "no", str(self.totp.now()))
        with self.assertRaises(AuthError):
            self.api.authenticate()

    @vcr.use_cassette("data/test-badotp.yml")
    def test_auth_badotp(self):
        self.api = API(self.server, self.username, self.password, "no")
        with self.assertRaises(AuthError):
            self.api.authenticate()

    def test_api_auth(self):
        self.assertTrue(isinstance(self.api.token, str))
        self.assertTrue(isinstance(self.api.token_expiration, datetime.datetime))
        self.assertTrue(isinstance(self.api.token_journalist_uuid, str))
        self.assertTrue(isinstance(self.api.first_name, (str, type(None))))
        self.assertTrue(isinstance(self.api.last_name, (str, type(None))))

    @vcr.use_cassette("data/test-seen.yml")
    def test_seen(self):
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

        self.assertTrue(
            self.api.seen(files=file_uuids, messages=message_uuids, replies=reply_uuids)
        )

    @vcr.use_cassette("data/test-get-sources.yml")
    def test_get_sources(self):
        sources = self.api.get_sources()
        for source in sources:
            # Assert expected fields are present
            assert source.journalist_designation
            assert source.uuid
            assert source.last_updated

    @vcr.use_cassette("data/test-star-add-remove.yml")
    def test_star_add_remove(self):
        s = self.api.get_sources()[0]
        self.assertTrue(self.api.add_star(s))
        self.assertTrue(self.api.remove_star(s))
        for source in self.api.get_sources():
            if source.uuid == s.uuid:
                self.assertFalse(source.is_starred)

    @vcr.use_cassette("data/test-get-single-source.yml")
    def test_get_single_source(self):
        s = self.api.get_sources()[0]
        # Now we will try to get the same source again
        s2 = self.api.get_source(s)

        self.assertEqual(s.journalist_designation, s2.journalist_designation)
        self.assertEqual(s.uuid, s2.uuid)

    @vcr.use_cassette("data/test-get-single-source.yml")
    def test_get_single_source_from_string(self):
        s = self.api.get_sources()[0]
        # Now we will try to get the same source again using uuid
        s2 = self.api.get_source_from_string(s.uuid)

        self.assertEqual(s.journalist_designation, s2.journalist_designation)
        self.assertEqual(s.uuid, s2.uuid)

    @vcr.use_cassette("data/test-failed-single-source.yml")
    def test_failed_single_source(self):
        with self.assertRaises(WrongUUIDError):
            self.api.get_source(Source(uuid="not there"))

    @vcr.use_cassette("data/test-get-submissions.yml")
    def test_get_submissions(self):
        s = self.api.get_sources()[0]

        subs = self.api.get_submissions(s)
        for submission in subs:
            assert submission.filename

    @vcr.use_cassette("data/test-get-submission.yml")
    def test_get_submission(self):
        # Get a source with submissions
        source_uuid = self.api.get_all_submissions()[0].source_uuid
        s = self.api.get_source(Source(uuid=source_uuid))

        subs = self.api.get_submissions(s)
        sub = self.api.get_submission(subs[0])
        self.assertEqual(sub.filename, subs[0].filename)

    @vcr.use_cassette("data/test-get-submission.yml")
    def test_get_submission_from_string(self):
        # Get a source with submissions
        source_uuid = self.api.get_all_submissions()[0].source_uuid
        s = self.api.get_source(Source(uuid=source_uuid))

        subs = self.api.get_submissions(s)
        sub = self.api.get_submission_from_string(subs[0].uuid, s.uuid)
        self.assertEqual(sub.filename, subs[0].filename)

    @vcr.use_cassette("data/test-get-wrong-submissions.yml")
    def test_get_wrong_submissions(self):
        s = self.api.get_sources()[0]
        s.uuid = "rofl-missing"
        with self.assertRaises(WrongUUIDError):
            self.api.get_submissions(s)

    @vcr.use_cassette("data/test-get-all-submissions.yml")
    def test_get_all_submissions(self):
        subs = self.api.get_all_submissions()
        for submission in subs:
            assert submission.filename

    @vcr.use_cassette("data/test-flag-source.yml")
    def test_flag_source(self):
        s = self.api.get_sources()[0]
        self.assertTrue(self.api.flag_source(s))
        # Now we will try to get the same source again
        s2 = self.api.get_source(s)
        self.assertTrue(s2.is_flagged)

    @vcr.use_cassette("data/test-delete-source.yml")
    def test_delete_source(self):
        number_of_sources_before = len(self.api.get_sources())

        s = self.api.get_sources()[0]
        self.assertTrue(self.api.delete_source(s))

        # Now there should be one less source
        sources = self.api.get_sources()
        self.assertEqual(len(sources), number_of_sources_before - 1)

    @vcr.use_cassette("data/test-delete-source.yml")
    def test_delete_source_from_string(self):
        number_of_sources_before = len(self.api.get_sources())

        s = self.api.get_sources()[0]
        self.assertTrue(self.api.delete_source_from_string(s.uuid))

        # Now there should be one less source
        sources = self.api.get_sources()
        self.assertEqual(len(sources), number_of_sources_before - 1)

    @vcr.use_cassette("data/test-delete-submission.yml")
    def test_delete_submission(self):
        number_of_submissions_before = len(self.api.get_all_submissions())

        subs = self.api.get_all_submissions()
        self.assertTrue(self.api.delete_submission(subs[0]))
        new_subs = self.api.get_all_submissions()
        # We now should have 1 less submission
        self.assertEqual(len(new_subs), number_of_submissions_before - 1)

        # Let us make sure that sub[0] is not there
        for s in new_subs:
            self.assertNotEqual(s.uuid, subs[0].uuid)

    @vcr.use_cassette("data/test-delete-submission-from-string.yml")
    def test_delete_submission_from_string(self):
        number_of_submissions_before = len(self.api.get_all_submissions())

        s = self.api.get_sources()[0]

        subs = self.api.get_submissions(s)

        self.assertTrue(self.api.delete_submission(subs[0]))
        new_subs = self.api.get_all_submissions()
        # We now should have 1 less submission
        self.assertEqual(len(new_subs), number_of_submissions_before - 1)

        # Let us make sure that sub[0] is not there
        for s in new_subs:
            self.assertNotEqual(s.uuid, subs[0].uuid)

    @vcr.use_cassette("data/test-get-current-user.yml")
    def test_get_current_user(self):
        user = self.api.get_current_user()
        self.assertTrue(user["is_admin"])
        self.assertEqual(user["username"], "journalist")
        self.assertTrue("first_name" in user)
        self.assertTrue("last_name" in user)

    @vcr.use_cassette("data/test-get-users.yml")
    def test_get_users(self):
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

    @vcr.use_cassette("data/test-error-unencrypted-reply.yml")
    def test_error_unencrypted_reply(self):
        s = self.api.get_sources()[0]
        with self.assertRaises(ReplyError) as err:
            self.api.reply_source(s, "hello")

        self.assertEqual(err.exception.msg, "bad request")

    @vcr.use_cassette("data/test-reply-source.yml")
    def test_reply_source(self):
        s = self.api.get_sources()[0]
        dirname = os.path.dirname(__file__)
        with open(os.path.join(dirname, "encrypted_msg.asc")) as fobj:
            data = fobj.read()

        reply = self.api.reply_source(s, data)
        assert isinstance(reply, Reply)
        assert reply.uuid
        assert reply.filename

    @vcr.use_cassette("data/test-reply-source-with-uuid.yml")
    def test_reply_source_with_uuid(self):
        s = self.api.get_sources()[0]
        dirname = os.path.dirname(__file__)
        with open(os.path.join(dirname, "encrypted_msg.asc")) as fobj:
            data = fobj.read()

        msg_uuid = "e467868c-1fbb-4b5e-bca2-87944ea83855"
        reply = self.api.reply_source(s, data, msg_uuid)
        assert reply.uuid == msg_uuid

    @vcr.use_cassette("data/test-download-submission.yml")
    def test_download_submission(self):
        submissions = self.api.get_all_submissions()
        unread_submission = None
        for s in submissions:
            if not s.is_read:
                unread_submission = s
                break

        if not unread_submission:
            self.assertFalse("There must be an unread submission in the db for this test to work.")

        self.assertFalse(unread_submission.is_read)

        # We need a temporary directory to download
        tmpdir = tempfile.mkdtemp()
        etag, filepath = self.api.download_submission(s, tmpdir)

        # now let us read the downloaded file
        with open(filepath, "rb") as fobj:
            content = fobj.read()

        # Verify the ETag contains the algorithm and the hash is correct
        hasher = hashlib.sha256()
        hasher.update(content)

        assert etag == "sha256:{}".format(hasher.hexdigest())

        # is_read should still be False as of SecureDrop 1.6.0 or later
        submission = self.api.get_submission(unread_submission)
        self.assertFalse(submission.is_read)

        # Let us remove the temporary directory
        shutil.rmtree(tmpdir)

    @vcr.use_cassette("data/test-get-replies-from-source.yml")
    def test_get_replies_from_source(self):
        s = self.api.get_sources()[0]
        replies = self.api.get_replies_from_source(s)
        self.assertEqual(len(replies), NUM_REPLIES_PER_SOURCE)

    @vcr.use_cassette("data/test-get-reply-from-source.yml")
    def test_get_reply_from_source(self):
        s = self.api.get_sources()[0]
        replies = self.api.get_replies_from_source(s)
        reply = replies[0]

        r = self.api.get_reply_from_source(s, reply.uuid)

        self.assertEqual(reply.filename, r.filename)
        self.assertEqual(reply.size, r.size)
        self.assertEqual(reply.reply_url, r.reply_url)
        self.assertEqual(reply.journalist_username, r.journalist_username)

    @vcr.use_cassette("data/test-get-all-replies.yml")
    def test_get_all_replies(self):
        num_sources = len(self.api.get_sources())
        replies = self.api.get_all_replies()
        self.assertEqual(len(replies), NUM_REPLIES_PER_SOURCE * num_sources)

    @vcr.use_cassette("data/test-download-reply.yml")
    def test_download_reply(self):
        r = self.api.get_all_replies()[0]

        # We need a temporary directory to download
        tmpdir = tempfile.mkdtemp()
        etag, filepath = self.api.download_reply(r, tmpdir)

        # now let us read the downloaded file
        with open(filepath, "rb") as fobj:
            content = fobj.read()

        # Verify the ETag contains the algorithm and the hash is correct
        hasher = hashlib.sha256()
        hasher.update(content)

        assert etag == "sha256:{}".format(hasher.hexdigest())

        # Let us remove the temporary directory
        shutil.rmtree(tmpdir)

    @vcr.use_cassette("data/test-delete-reply.yml")
    def test_delete_reply(self):
        r = self.api.get_all_replies()[0]

        number_of_replies_before = len(self.api.get_all_replies())

        self.assertTrue(self.api.delete_reply(r))

        # We deleted one, so there must be 1 less reply now
        self.assertEqual(len(self.api.get_all_replies()), number_of_replies_before - 1)

    @vcr.use_cassette("data/test-logout.yml")
    def test_zlogout(self):
        r = self.api.logout()
        self.assertTrue(r)


def test_request_connect_timeout(mocker):
    api = API("mock", "mock", "mock", "mock", proxy=False)
    mocker.patch("sdclientapi.requests.request", side_effect=ConnectTimeout)
    with pytest.raises(RequestTimeoutError):
        api.authenticate()


def test_request_read_timeout(mocker):
    api = API("mock", "mock", "mock", "mock", proxy=False)
    mocker.patch("sdclientapi.requests.request", side_effect=ReadTimeout)
    with pytest.raises(RequestTimeoutError):
        api.authenticate()


def test_download_reply_timeout(mocker):
    api = API("mock", "mock", "mock", "mock", proxy=False)
    mocker.patch("sdclientapi.requests.request", side_effect=RequestTimeoutError)
    with pytest.raises(RequestTimeoutError):
        r = Reply(uuid="humanproblem", filename="secret.txt")
        api.download_reply(r)


def test_download_submission_timeout(mocker):
    api = API("mock", "mock", "mock", "mock", proxy=False)
    mocker.patch("sdclientapi.requests.request", side_effect=RequestTimeoutError)
    with pytest.raises(RequestTimeoutError):
        s = Submission(uuid="climateproblem")
        api.download_submission(s)
