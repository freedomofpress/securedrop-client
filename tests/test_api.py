import os
import pyotp
import shutil
import tempfile
import time
import unittest
import vcr

from sdclientapi import API
from sdclientapi.sdlocalobjects import (
    BaseError,
    WrongUUIDError,
    ReplyError,
    Reply,
    Source,
)
from utils import load_auth, save_auth


class TestAPI(unittest.TestCase):
    @vcr.use_cassette("data/test-setup.yml")
    def setUp(self):
        self.totp = pyotp.TOTP("JHCOGO7VCER3EJ4L")
        self.username = "journalist"
        self.password = "correct horse battery staple profanity oil chewy"
        self.server = "http://127.0.0.1:8081/"
        self.api = API(self.server, self.username, self.password, str(self.totp.now()))
        for i in range(3):
            try:
                self.api.authenticate()
            except BaseError:
                token = load_auth()
                if token:
                    self.api.token = token
                    self.api.update_auth_header()
                    break
                time.sleep(31)

            save_auth(self.api.token)
            break

    def test_api_auth(self):
        self.assertTrue(self.api.token)

    @vcr.use_cassette("data/test-get-sources.yml")
    def test_get_sources(self):
        sources = self.api.get_sources()
        self.assertEqual(len(sources), 2)

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
        self.assertEqual(len(subs), 2)

    @vcr.use_cassette("data/test-get-submission.yml")
    def test_get_submission(self):
        s = self.api.get_sources()[0]

        subs = self.api.get_submissions(s)
        sub = self.api.get_submission(subs[0])
        self.assertEqual(sub.filename, subs[0].filename)

    @vcr.use_cassette("data/test-get-submission.yml")
    def test_get_submission_from_string(self):
        s = self.api.get_sources()[0]

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
        self.assertEqual(len(subs), 4)

    @vcr.use_cassette("data/test-flag-source.yml")
    def test_flag_source(self):
        s = self.api.get_sources()[0]
        self.assertTrue(self.api.flag_source(s))
        # Now we will try to get the same source again
        s2 = self.api.get_source(s)
        self.assertTrue(s2.is_flagged)

    @vcr.use_cassette("data/test-delete-source.yml")
    def test_delete_source(self):
        s = self.api.get_sources()[0]
        self.assertTrue(self.api.delete_source(s))

        # Now there should be one source left
        sources = self.api.get_sources()
        self.assertEqual(len(sources), 1)

    @vcr.use_cassette("data/test-delete-source.yml")
    def test_delete_source_from_string(self):
        s = self.api.get_sources()[0]
        self.assertTrue(self.api.delete_source_from_string(s.uuid))

        # Now there should be one source left
        sources = self.api.get_sources()
        self.assertEqual(len(sources), 1)

    @vcr.use_cassette("data/test-delete-submission.yml")
    def test_delete_submission(self):
        subs = self.api.get_all_submissions()
        self.assertTrue(self.api.delete_submission(subs[0]))
        new_subs = self.api.get_all_submissions()
        # We now should have 3 submissions
        self.assertEqual(len(new_subs), 3)

        # Let us make sure that sub[0] is not there
        for s in new_subs:
            self.assertNotEqual(s.uuid, subs[0].uuid)

    @vcr.use_cassette("data/test-delete-submission-from-string.yml")
    def test_delete_submission_from_string(self):
        s = self.api.get_sources()[0]

        subs = self.api.get_submissions(s)

        self.assertTrue(self.api.delete_submission(subs[0]))
        new_subs = self.api.get_all_submissions()
        # We now should have 3 submissions
        self.assertEqual(len(new_subs), 3)

        # Let us make sure that sub[0] is not there
        for s in new_subs:
            self.assertNotEqual(s.uuid, subs[0].uuid)

    @vcr.use_cassette("data/test-get-current-user.yml")
    def test_get_current_user(self):
        user = self.api.get_current_user()
        self.assertTrue(user["is_admin"])
        self.assertEqual(user["username"], "journalist")

    @vcr.use_cassette("data/test-error-unencrypted-reply.yml")
    def test_error_unencrypted_reply(self):
        s = self.api.get_sources()[0]
        with self.assertRaises(ReplyError) as err:
            self.api.reply_source(s, "hello")

        self.assertEqual(err.exception.msg, "You must encrypt replies client side")

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
        s = self.api.get_all_submissions()[0]

        self.assertFalse(s.is_read)

        # We need a temporary directory to download
        tmpdir = tempfile.mkdtemp()
        _, filepath = self.api.download_submission(s, tmpdir)

        # now let us read the downloaded file
        with open(filepath, "rb") as fobj:
            fobj.read()

        # Now the submission should have is_read as True.

        s = self.api.get_submission(s)
        self.assertTrue(s.is_read)

        # Let us remove the temporary directory
        shutil.rmtree(tmpdir)

    @vcr.use_cassette("data/test-get-replies-from-source.yml")
    def test_get_replies_from_source(self):
        s = self.api.get_sources()[0]
        replies = self.api.get_replies_from_source(s)
        self.assertEqual(len(replies), 2)

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
        replies = self.api.get_all_replies()
        self.assertEqual(len(replies), 4)

    @vcr.use_cassette("data/test-download-reply.yml")
    def test_download_reply(self):
        r = self.api.get_all_replies()[0]

        # We need a temporary directory to download
        tmpdir = tempfile.mkdtemp()
        _, filepath = self.api.download_reply(r, tmpdir)

        # now let us read the downloaded file
        with open(filepath, "rb") as fobj:
            fobj.read()

        # Let us remove the temporary directory
        shutil.rmtree(tmpdir)

    @vcr.use_cassette("data/test-delete-reply.yml")
    def test_delete_reply(self):
        r = self.api.get_all_replies()[0]

        self.assertTrue(self.api.delete_reply(r))

        # We deleted one, so there must be 3 replies left
        self.assertEqual(len(self.api.get_all_replies()), 3)
