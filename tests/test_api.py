from pprint import pprint
import os
import time
import json
import unittest
from sdclientapi import *

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

    def test_get_sources(self):
        sources = self.api.get_sources()
        assert len(sources) == 2

    def test_star_add_remove(self):
        s = self.api.get_sources()[0]
        assert self.api.add_star(s)
        assert self.api.remove_star(s)
        for source in self.api.get_sources():
            if source.uuid == s.uuid:
                assert not source.is_starred
