import http
import json
import os
import shutil
import tempfile
import time
from subprocess import TimeoutExpired

import pyotp
import pytest

from sdclientapi import API, RequestTimeoutError
from sdclientapi.sdlocalobjects import BaseError, Reply, Submission
from test_shared import TestShared
from utils import dastollervey_datasaver, load_auth, save_auth


class TestAPIProxy(TestShared):
    """
    Note that TestShared contains most of the test code, which is shared between
    API and API Proxy tests.
    """

    @dastollervey_datasaver
    def setUp(self):
        self.totp = pyotp.TOTP("JHCOGO7VCER3EJ4L")
        self.username = "journalist"
        self.password = "correct horse battery staple profanity oil chewy"
        self.server = "http://localhost:8081/"
        self.api = API(self.server, self.username, self.password, str(self.totp.now()), proxy=True)

        for i in range(3):
            if os.path.exists("testtoken.json"):
                token = load_auth()
                self.api.token = token
                self.api.update_auth_header()
                break

            # The following is True when we did a logout
            if os.path.exists("logout.txt"):
                os.unlink("logout.txt")
                time.sleep(31)
            # Now let us try to login
            try:
                self.api = API(
                    self.server, self.username, self.password, str(self.totp.now()), proxy=True
                )
                self.api.authenticate()
                with open("login.txt", "w") as fobj:
                    fobj.write("in")
            except Exception as err:
                print(err)
                time.sleep(31)
                continue

            save_auth(self.api.token)
            break

    def test_api_auth(self):
        super().api_auth()

    @dastollervey_datasaver
    def test_seen(self):
        super().seen()

    @dastollervey_datasaver
    def test_get_sources(self):
        super().get_sources()

    @dastollervey_datasaver
    def test_star_add_remove(self):
        super().star_add_remove()

    @dastollervey_datasaver
    def test_get_single_source(self):
        super().get_single_source()

    @dastollervey_datasaver
    def test_get_single_source_from_string(self):
        super().get_single_source(from_string=True)

    @dastollervey_datasaver
    def test_failed_single_source(self):
        super().failed_single_source()

    @dastollervey_datasaver
    def test_get_submissions(self):
        super().get_submissions()

    @dastollervey_datasaver
    def test_get_submission(self):
        super().get_submission()

    @dastollervey_datasaver
    def test_get_submission_from_string(self):
        super().get_submission(from_string=True)

    @dastollervey_datasaver
    def test_get_wrong_submissions(self):
        super().get_wrong_submissions()

    @dastollervey_datasaver
    def test_get_all_submissions(self):
        super().get_all_submissions()

    @dastollervey_datasaver
    def test_flag_source(self):
        super().flag_source()

    @dastollervey_datasaver
    def test_delete_source(self):
        super().delete_source()

    @dastollervey_datasaver
    def test_delete_source_from_string(self):
        super().delete_source(from_string=True)

    @dastollervey_datasaver
    def test_delete_submission(self):
        super().delete_submission()

    @dastollervey_datasaver
    def test_delete_submission_from_string(self):
        super().delete_submission(from_string=True)

    @dastollervey_datasaver
    def test_get_current_user(self):
        super().get_current_user()

    @dastollervey_datasaver
    def test_get_users(self):
        super().get_users()

    @dastollervey_datasaver
    def test_error_unencrypted_reply(self):
        super().error_unencrypted_reply()

    @dastollervey_datasaver
    def test_reply_source(self):
        super().reply_source()

    @dastollervey_datasaver
    def test_reply_source_with_uuid(self):
        super().reply_source_with_uuid()

    @dastollervey_datasaver
    def test_get_replies_from_source(self):
        super().get_replies_from_source()

    @dastollervey_datasaver
    def test_get_reply_from_source(self):
        super().get_reply_from_source()

    @dastollervey_datasaver
    def test_get_all_replies(self):
        super().get_all_replies()

    @dastollervey_datasaver
    def test_delete_reply(self):
        super().delete_reply()

    @dastollervey_datasaver
    def test_download_reply(self):
        r = self.api.get_all_replies()[0]

        # We need a temporary directory to download
        tmpdir = tempfile.mkdtemp()
        _, filepath = self.api.download_reply(r, tmpdir)

        # Uncomment the following part only on QubesOS
        # for testing against real server.
        # now let us read the downloaded file
        # with open(filepath, "rb") as fobj:
        #     fobj.read()

        # Let us remove the temporary directory
        shutil.rmtree(tmpdir)

    @dastollervey_datasaver
    def test_download_submission(self):
        s = self.api.get_all_submissions()[0]

        self.assertFalse(s.is_read)

        # We need a temporary directory to download
        tmpdir = tempfile.mkdtemp()
        _, filepath = self.api.download_submission(s, tmpdir)

        # Uncomment the following part only on QubesOS
        # for testing against real server.
        # now let us read the downloaded file
        # with open(filepath, "rb") as fobj:
        #    fobj.read()

        # is_read should still be False as of SecureDrop 1.6.0 or later.

        s = self.api.get_submission(s)
        self.assertFalse(s.is_read)

        # Let us remove the temporary directory
        shutil.rmtree(tmpdir)

    @dastollervey_datasaver
    def test_logout(self):
        r = self.api.logout()
        self.assertTrue(r)
        if os.path.exists("login.txt"):
            os.unlink("login.txt")
        if os.path.exists("testtoken.json"):
            os.unlink("testtoken.json")
        with open("logout.txt", "w") as fobj:
            fobj.write("out")


def test_request_timeout(mocker):
    class MockedPopen:
        def __init__(self, *nargs, **kwargs) -> None:
            self.stdin = mocker.MagicMock()

        def communicate(self, *nargs, **kwargs) -> None:
            raise TimeoutExpired(["mock"], 123)

    api = API("mock", "mock", "mock", "mock", proxy=True)
    mocker.patch("sdclientapi.Popen", MockedPopen)

    with pytest.raises(RequestTimeoutError):
        api.authenticate()


def test_download_reply_timeout(mocker):
    class MockedPopen:
        def __init__(self, *nargs, **kwargs) -> None:
            self.stdin = mocker.MagicMock()

        def communicate(self, *nargs, **kwargs) -> None:
            raise TimeoutExpired(["mock"], 123)

    api = API("mock", "mock", "mock", "mock", proxy=True)
    mocker.patch("sdclientapi.Popen", MockedPopen)
    with pytest.raises(RequestTimeoutError):
        r = Reply(uuid="humanproblem", filename="secret.txt")
        api.download_reply(r)


def test_download_submission_timeout(mocker):
    class MockedPopen:
        def __init__(self, *nargs, **kwargs) -> None:
            self.stdin = mocker.MagicMock()

        def communicate(self, *nargs, **kwargs) -> None:
            raise TimeoutExpired(["mock"], 123)

    api = API("mock", "mock", "mock", "mock", proxy=True)
    mocker.patch("sdclientapi.Popen", MockedPopen)
    with pytest.raises(RequestTimeoutError):
        s = Submission(uuid="climateproblem")
        api.download_submission(s)


def test_download_get_sources_error_request_timeout(mocker):
    api = API("mock", "mock", "mock", "mock", True)
    mocker.patch(
        "sdclientapi.json_query",
        return_value=(
            json.dumps(
                {
                    "body": json.dumps({"error": "wah"}),
                    "status": http.HTTPStatus.GATEWAY_TIMEOUT,
                    "headers": "foo",
                }
            )
        ),
    )
    with pytest.raises(RequestTimeoutError):
        api.get_sources()


def test_filename_key_not_in_download_response(mocker):
    api = API("mock", "mock", "mock", "mock", True)
    s = Submission(uuid="foobar")
    mocker.patch(
        "sdclientapi.json_query",
        return_value=(
            json.dumps({"body": json.dumps({"error": "wah"}), "status": 200, "headers": "foo"})
        ),
    )
    with pytest.raises(BaseError):
        api.download_submission(s)
