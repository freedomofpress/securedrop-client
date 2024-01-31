import hashlib
import shutil
import tempfile
import time

import pyotp
import pytest
import vcr
from test_shared import TestShared
from utils import VCRAPI

from securedrop_client.sdk import API, RequestTimeoutError, ServerConnectionError
from securedrop_client.sdk.sdlocalobjects import AuthError, Reply, Submission

NUM_REPLIES_PER_SOURCE = 2


class TestAPI(TestShared):
    """
    Tests here used to call helper methods (without the `test_` prefix) in
    `TestShared`, because some were implemented differently in `TestAPIProxy`,
    which was intended to be run on Qubes with `qrexec` available.  This is now
    the only test module and path, but the separation from `TestShared` is still
    useful, since these test methods must be run in order while recording VCR.py
    cassettes via `utils.VCRAPI`.
    """

    @VCRAPI.use_cassette
    def setup_method(self):
        self.totp = pyotp.TOTP("JHCOGO7VCER3EJ4L")
        self.username = "journalist"
        self.password = "correct horse battery staple profanity oil chewy"
        self.server = "http://localhost:8081/"
        self.api = VCRAPI(self.server, self.username, self.password, str(self.totp.now()))
        try:
            self.api.authenticate()
        except BaseError as err:
            raise AuthError(
                "Could not obtain API token during test setup. "
                "TOTP code may have expired or proxy may not be reachable. "
                "Error was: {}".format(err.msg)
            )

    @VCRAPI.use_cassette
    def test_auth_baduser(self):
        self.api = VCRAPI(self.server, "no", self.password, str(self.totp.now()))
        with pytest.raises(AuthError):
            self.api.authenticate()

    @VCRAPI.use_cassette
    def test_auth_badpassword(self):
        self.api = VCRAPI(self.server, self.username, "no", str(self.totp.now()))
        with pytest.raises(AuthError):
            self.api.authenticate()

    @VCRAPI.use_cassette
    def test_auth_badotp(self):
        self.api = VCRAPI(self.server, self.username, self.password, "no")
        with pytest.raises(AuthError):
            self.api.authenticate()

    @VCRAPI.use_cassette
    def test_api_auth(self):
        super().api_auth()

    # This test is order-sensitive and must be run before the "seen"
    # state of files is altered.
    @VCRAPI.use_cassette
    def test_download_submission(self):
        submissions = self.api.get_all_submissions()
        unread_submission = None
        for s in submissions:
            if not s.is_read:
                unread_submission = s
                break

        if not unread_submission:
            assert False, "There must be an unread submission in the db for this test to work."

        assert not unread_submission.is_read

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
        assert not submission.is_read

        # Let us remove the temporary directory
        shutil.rmtree(tmpdir)

    @VCRAPI.use_cassette
    def test_seen(self):
        super().seen()

    @VCRAPI.use_cassette
    def test_get_sources(self):
        super().get_sources()

    @VCRAPI.use_cassette
    def test_star_add_remove(self):
        super().star_add_remove()

    @VCRAPI.use_cassette
    def test_get_single_source(self):
        super().get_single_source()

    @VCRAPI.use_cassette
    def test_get_single_source_from_string(self):
        super().get_single_source(from_string=True)

    @VCRAPI.use_cassette
    def test_failed_single_source(self):
        super().failed_single_source()

    @VCRAPI.use_cassette
    def test_get_submissions(self):
        super().get_submissions()

    @VCRAPI.use_cassette
    def test_get_submission(self):
        super().get_submission()

    @VCRAPI.use_cassette
    def test_get_submission_from_string(self):
        super().get_submission(from_string=True)

    @VCRAPI.use_cassette
    def test_get_wrong_submissions(self):
        super().get_wrong_submissions()

    @VCRAPI.use_cassette
    def test_get_all_submissions(self):
        super().get_all_submissions()

    @VCRAPI.use_cassette
    def test_flag_source(self):
        super().flag_source()

    @VCRAPI.use_cassette
    def test_get_current_user(self):
        super().get_current_user()

    @VCRAPI.use_cassette
    def test_get_users(self):
        super().get_users()

    @VCRAPI.use_cassette
    def test_error_unencrypted_reply(self):
        super().error_unencrypted_reply()

    @VCRAPI.use_cassette
    def test_get_replies_from_source(self):
        super().get_replies_from_source()

    @VCRAPI.use_cassette
    def test_get_reply_from_source(self):
        super().get_reply_from_source()

    @VCRAPI.use_cassette
    def test_get_all_replies(self):
        super().get_all_replies()

    @VCRAPI.use_cassette
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

    # ORDER MATTERS: The following tests add or delete data, and should
    # not be run before other tests, which may rely on the original fixture
    # state.

    @VCRAPI.use_cassette
    def test_reply_source(self):
        super().reply_source()

    @VCRAPI.use_cassette
    def test_reply_source_with_uuid(self):
        super().reply_source_with_uuid()

    @VCRAPI.use_cassette
    def test_delete_conversation(self):
        super().delete_conversation()

    @VCRAPI.use_cassette
    def test_delete_source(self):
        super().delete_source()

    @VCRAPI.use_cassette
    def test_delete_source_from_string(self):
        super().delete_source(from_string=True)

    @VCRAPI.use_cassette
    def test_delete_submission(self):
        super().delete_submission()

    @VCRAPI.use_cassette
    def test_delete_submission_from_string(self):
        super().delete_submission(from_string=True)

    @VCRAPI.use_cassette
    def test_delete_reply(self):
        super().delete_reply()

    @VCRAPI.use_cassette
    def test_zlogout(self):
        r = self.api.logout()
        assert r


def test_request_connect_timeout(mocker):
    api = API("mock", "mock", "mock", "mock", proxy=False)
    mocker.patch("securedrop_client.sdk.API._send_json_request", side_effect=ServerConnectionError)
    with pytest.raises(ServerConnectionError):
        api.authenticate()


def test_request_read_timeout(mocker):
    api = API("mock", "mock", "mock", "mock", proxy=False)
    mocker.patch("securedrop_client.sdk.API._send_json_request", side_effect=RequestTimeoutError)
    with pytest.raises(RequestTimeoutError):
        api.authenticate()


def test_download_reply_timeout(mocker):
    api = API("mock", "mock", "mock", "mock", proxy=False)
    mocker.patch("securedrop_client.sdk.API._send_json_request", side_effect=RequestTimeoutError)
    with pytest.raises(RequestTimeoutError):
        r = Reply(uuid="humanproblem", filename="secret.txt")
        api.download_reply(r)


def test_download_submission_timeout(mocker):
    api = API("mock", "mock", "mock", "mock", proxy=False)
    mocker.patch("securedrop_client.sdk.API._send_json_request", side_effect=RequestTimeoutError)
    with pytest.raises(RequestTimeoutError):
        s = Submission(uuid="climateproblem")
        api.download_submission(s)
