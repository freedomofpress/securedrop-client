from pprint import pprint
import os
import time
import json
import unittest
from sdclientapi import *

import vcr
import pyotp


def load_auth():
    "Helper function to load token"
    if os.path.exists("testtoken.json"):
        with open("testtoken.json") as fobj:
            return json.load(fobj)
    return None


def save_auth(token):
    with open("testtoken.json", "w") as fobj:
        json.dump(token, fobj)


class TestAPI(unittest.TestCase):
    @vcr.use_cassette("data/test-setup.yml")
    def setUp(self):
        self.totp = pyotp.TOTP("JHCOGO7VCER3EJ4L")
        self.username = "journalist"
        self.password = "correct horse battery staple profanity oil chewy"
        self.server = "http://localhost:8081/"
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
        assert self.api.token

    @vcr.use_cassette("data/test-get-sources.yml")
    def test_get_sources(self):
        sources = self.api.get_sources()
        assert len(sources) == 2

    @vcr.use_cassette("data/test-star-add-remove.yml")
    def test_star_add_remove(self):
        s = self.api.get_sources()[0]
        assert self.api.add_star(s)
        assert self.api.remove_star(s)
        for source in self.api.get_sources():
            if source.uuid == s.uuid:
                assert not source.is_starred

    @vcr.use_cassette("data/test-get-single-source.yml")
    def test_get_single_source(self):
        s = self.api.get_sources()[0]
        # Now we will try to get the same source again
        s2 = self.api.get_source(s.uuid)

        assert s.journalist_designation == s2.journalist_designation
        assert s.uuid == s2.uuid

    @vcr.use_cassette("data/test-failed-single-source.yml")
    def test_failed_single_source(self):
        with self.assertRaises(WrongUUIDError):
            self.api.get_source("not there")

    @vcr.use_cassette("data/test-get-submissions.yml")
    def test_get_submissions(self):
        s = self.api.get_sources()[0]

        subs = self.api.get_submissions(s)
        assert len(subs) == 2

    @vcr.use_cassette("data/test-get-wrong-submissions.yml")
    def test_get_wrong_submissions(self):
        s = self.api.get_sources()[0]
        s.submissions_url = "/api/v1/sources/rofl-missing/submissions/2334"
        with self.assertRaises(WrongUUIDError):
            self.api.get_submissions(s)

    @vcr.use_cassette("data/test-get-all-submissions.yml")
    def test_get_all_submissions(self):
        subs = self.api.get_all_submissions()
        assert len(subs) == 4

    @vcr.use_cassette("data/test-flag-source.yml")
    def test_flag_source(self):
        s = self.api.get_sources()[0]
        assert self.api.flag_source(s)
        # Now we will try to get the same source again
        s2 = self.api.get_source(s.uuid)
        assert s2.is_flagged

    @vcr.use_cassette("data/test-delete-source.yml")
    def test_delete_source(self):
        s = self.api.get_sources()[0]
        assert self.api.delete_source(s.uuid)

        # Now there should be one source left
        sources = self.api.get_sources()
        assert len(sources) == 1
