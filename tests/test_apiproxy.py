from pprint import pprint
import os
import time
import json
import hashlib
import shutil
import tempfile
import unittest
from sdclientapi import *

from utils import *
import pyotp


class TestAPIProxy(unittest.TestCase):
    @dastollervey_datasaver
    def setUp(self):
        self.totp = pyotp.TOTP("JHCOGO7VCER3EJ4L")
        self.username = "journalist"
        self.password = "correct horse battery staple profanity oil chewy"
        self.server = "http://localhost:8081/"
        self.api = APIProxy(self.server, self.username, self.password, str(self.totp.now()))
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

    @dastollervey_datasaver
    def test_get_sources(self):
        sources = self.api.get_sources()
        self.assertEqual(len(sources), 2)
    
    @dastollervey_datasaver
    def test_star_add_remove(self):
        s = self.api.get_sources()[0]
        self.assertTrue(self.api.add_star(s))
        self.assertTrue(self.api.remove_star(s))
        for source in self.api.get_sources():
            if source.uuid == s.uuid:
                self.assertFalse(source.is_starred)

    @dastollervey_datasaver
    def test_get_single_source(self):
        s = self.api.get_sources()[0]
        # Now we will try to get the same source again
        s2 = self.api.get_source(s)

        self.assertEqual(s.journalist_designation, s2.journalist_designation)
        self.assertEqual(s.uuid, s2.uuid)

    @dastollervey_datasaver
    def test_get_single_source_from_string(self):
        s = self.api.get_sources()[0]
        # Now we will try to get the same source again using uuid
        s2 = self.api.get_source_from_string(s.uuid)

        self.assertEqual(s.journalist_designation, s2.journalist_designation)
        self.assertEqual(s.uuid, s2.uuid)

    @dastollervey_datasaver
    def test_failed_single_source(self):
        with self.assertRaises(WrongUUIDError):
            self.api.get_source(Source(uuid="not there"))

    @dastollervey_datasaver
    def test_get_submissions(self):
        s = self.api.get_sources()[0]

        subs = self.api.get_submissions(s)
        self.assertEqual(len(subs), 2)

    @dastollervey_datasaver
    def test_get_submission(self):
        s = self.api.get_sources()[0]

        subs = self.api.get_submissions(s)
        sub = self.api.get_submission(subs[0])
        self.assertEqual(sub.filename, subs[0].filename)

    @dastollervey_datasaver
    def test_get_submission_from_string(self):
        s = self.api.get_sources()[0]

        subs = self.api.get_submissions(s)
        sub = self.api.get_submission_from_string(subs[0].uuid, s.uuid)
        self.assertEqual(sub.filename, subs[0].filename)

    @dastollervey_datasaver
    def test_get_wrong_submissions(self):
        s = self.api.get_sources()[0]
        s.submissions_url = "/api/v1/sources/rofl-missing/submissions/2334"
        s.uuid = "rofl-missing"
        with self.assertRaises(WrongUUIDError):
            self.api.get_submissions(s)

    @dastollervey_datasaver
    def test_get_all_submissions(self):
        subs = self.api.get_all_submissions()
        self.assertEqual(len(subs), 4)

    @dastollervey_datasaver
    def test_flag_source(self):
        s = self.api.get_sources()[0]
        self.assertTrue(self.api.flag_source(s))
        # Now we will try to get the same source again
        s2 = self.api.get_source(s)
        self.assertTrue(s2.is_flagged)

    @dastollervey_datasaver
    def test_delete_source(self):
        s = self.api.get_sources()[0]
        self.assertTrue(self.api.delete_source(s))

        # Now there should be one source left
        sources = self.api.get_sources()
        self.assertEqual(len(sources), 1)

    @dastollervey_datasaver
    def test_delete_source_from_string(self):
        s = self.api.get_sources()[0]
        self.assertTrue(self.api.delete_source_from_string(s.uuid))

        # Now there should be one source left
        sources = self.api.get_sources()
        self.assertEqual(len(sources), 1)

    @dastollervey_datasaver
    def test_delete_submission(self):
        subs = self.api.get_all_submissions()
        self.assertTrue(self.api.delete_submission(subs[0]))
        new_subs = self.api.get_all_submissions()
        # We now should have 3 submissions
        self.assertEqual(len(new_subs), 3)

        # Let us make sure that sub[0] is not there
        for s in new_subs:
            self.assertNotEqual(s.uuid, subs[0].uuid)

    @dastollervey_datasaver
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

    @dastollervey_datasaver
    def test_get_current_user(self):
        user = self.api.get_current_user()
        self.assertTrue(user["is_admin"])
        self.assertEqual(user["username"], "journalist")

    @dastollervey_datasaver
    def test_error_unencrypted_reply(self):
        s = self.api.get_sources()[0]
        with self.assertRaises(ReplyError) as err:
            self.api.reply_source(s, "hello")

        self.assertEqual(err.exception.msg, "You must encrypt replies client side")

    @dastollervey_datasaver
    def test_reply_source(self):
        s = self.api.get_sources()[0]
        dirname = os.path.dirname(__file__)
        with open(os.path.join(dirname, "encrypted_msg.asc")) as fobj:
            data = fobj.read()

        self.assertTrue(self.api.reply_source(s, data))

    @dastollervey_datasaver
    def test_get_replies_from_source(self):
        s = self.api.get_sources()[0]
        replies = self.api.get_replies_from_source(s)
        self.assertEqual(len(replies), 2)

    @dastollervey_datasaver
    def test_get_reply_from_source(self):
        s = self.api.get_sources()[0]
        replies = self.api.get_replies_from_source(s)
        reply = replies[0]

        r = self.api.get_reply_from_source(s, reply.uuid)

        self.assertEqual(reply.filename, r.filename)
        self.assertEqual(reply.size, r.size)
        self.assertEqual(reply.reply_url, r.reply_url)
        self.assertEqual(reply.journalist_username, r.journalist_username)

    @dastollervey_datasaver
    def test_get_all_replies(self):
        replies = self.api.get_all_replies()
        self.assertEqual(len(replies), 4)

    @dastollervey_datasaver
    def test_delete_reply(self):
        r = self.api.get_all_replies()[0]

        self.assertTrue(self.api.delete_reply(r))

        # We deleted one, so there must be 3 replies left
        self.assertEqual(len(self.api.get_all_replies()), 3)

    @dastollervey_datasaver
    def test_download_reply(self):
        r = self.api.get_all_replies()[0]

        etag, filepath = self.api.download_reply(r)

    @dastollervey_datasaver
    def test_download_submission(self):
        s = self.api.get_all_submissions()[0]

        self.assertFalse(s.is_read)

        etag, filepath = self.api.download_submission(s)

        # Now the submission should have is_read as True.
        s = self.api.get_submission(s)
        self.assertTrue(s.is_read)
