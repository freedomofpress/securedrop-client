import hashlib
import json
import os
import shlex
import shutil
import subprocess
import tempfile

import pyotp
import pytest
from test_shared import TestShared
from utils import VCRAPI

from securedrop_client.sdk import API, RequestTimeoutError, ServerConnectionError
from securedrop_client.sdk.sdlocalobjects import (
    AuthError,
    BaseError,
    Reply,
    Submission,
    WrongUUIDError,
)

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
                f"Error was: {err.msg}"
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
            pytest.fail("There must be an unread submission in the db for this test to work.")

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

        assert etag == f"sha256:{hasher.hexdigest()}"

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
    def test_failed_single_source(self):
        super().failed_single_source()

    @VCRAPI.use_cassette
    def test_get_submissions(self):
        super().get_submissions()

    @VCRAPI.use_cassette
    def test_get_submission(self):
        super().get_submission()

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

        assert etag == f"sha256:{hasher.hexdigest()}"

        # Let us remove the temporary directory
        shutil.rmtree(tmpdir)

    @VCRAPI.use_cassette
    def test_download_submission_autoresume(self, mocker):
        # Get a submision
        submissions = self.api.get_all_submissions()
        for s in submissions:
            if s.is_file():
                submission = s
                break

        # Get the submission's content
        with tempfile.TemporaryDirectory() as tmpdir:
            _, filepath = self.api.download_submission(submission, tmpdir)
            with open(filepath, "rb") as fobj:
                content = fobj.read()

        # Stub subprocess.Popen to raise a subprocess.TimeoutExpired, to simulate an interrupted
        # download after 200 bytes
        class StubbedStdout:
            def __init__(self):
                self.counter = 0
                self.closed = False

            def read(self, n=-1):
                if self.counter >= 200:
                    # Restore the original Popen before raising the exception
                    mocker.stopall()
                    raise subprocess.TimeoutExpired(
                        cmd=None, timeout=None, output=None, stderr=None
                    )
                chunk = content[self.counter : self.counter + n]
                self.counter += len(chunk)
                return chunk

            def close(self):
                self.closed = True

            def fileno(self):
                return 1

        class StubbedStderr:
            def __init__(self):
                self.closed = False

            def read(self, n=-1):
                return json.dumps(
                    {
                        "headers": {
                            "content-type": "application/pgp-encrypted",
                            "etag": "sha256:3aa5ec3fe60b235a76bfc2c3a5c5d525687f04c1670060632a21b6a77c131f65",  # noqa: E501
                            "content-disposition": "attachment; filename=3-assessable_firmness-doc.gz.gpg",  # noqa: E501
                            "content-length": "651",
                            "accept-ranges": "bytes",
                        }
                    }
                ).encode()

            def close(self):
                self.closed = True

            def fileno(self):
                return 2

        class StubbedPopen(subprocess.Popen):
            def __init__(self, *args, content="", **kwargs):
                super().__init__(*args, **kwargs)

                # Only stub if the command contains "securedrop.Proxy" or "securedrop-proxy"
                cmd = shlex.join(args[0])
                if "securedrop.Proxy" in cmd or "securedrop-proxy" in cmd:
                    self._is_securedrop_proxy = True
                    self.stdout = StubbedStdout()
                    self.stderr = StubbedStderr()
                else:
                    self._is_securedrop_proxy = False

            def wait(self, timeout=None):
                if self._is_securedrop_proxy:
                    return 0
                else:
                    return super().wait()

        # Download again, with the stubbed Popen
        mocker.patch("subprocess.Popen", new=StubbedPopen)
        with tempfile.TemporaryDirectory() as tmpdir:
            etag, filepath = self.api.download_submission(submission, tmpdir)
            with open(filepath, "rb") as fobj:
                new_content = fobj.read()

        # Verify the content is the same
        assert content == new_content

        mocker.stopall()

    @VCRAPI.use_cassette
    def test_download_submission_autoresume_fail(self, mocker):
        # Get a submision
        submissions = self.api.get_all_submissions()
        for s in submissions:
            if s.is_file():
                submission = s
                break

        # Stub subprocess.Popen to raise a subprocess.TimeoutExpired every time
        class StubbedPopen(subprocess.Popen):
            def __init__(self, *args, content="", **kwargs):
                super().__init__(*args, **kwargs)

                # Only stub if the command contains "securedrop.Proxy" or "securedrop-proxy"
                cmd = shlex.join(args[0])
                if "securedrop.Proxy" in cmd or "securedrop-proxy" in cmd:
                    raise subprocess.TimeoutExpired(
                        cmd=None, timeout=None, output=None, stderr=None
                    )

        mocker.patch("subprocess.Popen", new=StubbedPopen)

        # Download with the stubbed Popen
        tmpdir = tempfile.TemporaryDirectory()
        with pytest.raises(RequestTimeoutError):
            self.api.download_submission(submission, tmpdir.name)
        tmpdir.cleanup()

        mocker.stopall()

    @VCRAPI.use_cassette
    def test_download_submission_stream_404(self):
        # Get a submision
        submissions = self.api.get_all_submissions()
        for s in submissions:
            if s.is_file():
                submission = s
                break

        # Modify it so that it will return a 404 error
        submission.uuid += "404"

        # Download it
        tmpdir = tempfile.TemporaryDirectory()
        with pytest.raises(WrongUUIDError):
            self.api.download_submission(submission, tmpdir.name)
        tmpdir.cleanup()

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
    def test_delete_submission(self):
        super().delete_submission()

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
    r = Reply(uuid="humanproblem", filename="secret.txt")
    tmpdir = tempfile.mkdtemp()
    with pytest.raises(RequestTimeoutError):
        api.download_reply(r, tmpdir)


def test_download_submission_timeout(mocker):
    api = API("mock", "mock", "mock", "mock", proxy=False)
    mocker.patch("securedrop_client.sdk.API._send_json_request", side_effect=RequestTimeoutError)
    tmpdir = tempfile.TemporaryDirectory()
    s = Submission(
        uuid="climateproblem",
        filename="secret.txt",
        download_url="http://mock",
        is_read=False,
        size=1000,
        source_url="http://mock",
        submission_url="http://mock",
        seen_by=False,
    )
    with pytest.raises(RequestTimeoutError):
        api.download_submission(s, tmpdir.name)
    tmpdir.cleanup()

    # Delete secret.txt, if it exists
    try:
        os.remove("secret.txt")
    except FileNotFoundError:
        pass
