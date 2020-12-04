import http
import json
import shutil
import tempfile
from subprocess import TimeoutExpired

import pyotp
import pytest

from sdclientapi import API, RequestTimeoutError
from sdclientapi.sdlocalobjects import AuthError, BaseError, Reply, Submission
from test_shared import TestShared
from utils import qrexec_datasaver


class TestAPIProxy(TestShared):
    """
    Note that TestShared contains most of the test code, which is shared between
    API and API Proxy tests.
    """

    @qrexec_datasaver
    def setup_method(self):
        self.totp = pyotp.TOTP("JHCOGO7VCER3EJ4L")
        self.username = "journalist"
        self.password = "correct horse battery staple profanity oil chewy"
        self.server = "http://localhost:8081/"
        self.api = API(self.server, self.username, self.password, str(self.totp.now()), proxy=True)
        auth_result = None
        try:
            auth_result = self.api.authenticate()
        except Exception as err:
            print(err)

        if auth_result is None:
            raise AuthError(
                "Could not obtain API token during test setup. TOTP code may have expired."
            )

    @qrexec_datasaver
    def test_api_auth(self):
        super().api_auth()

    # This test is order-sensitive and must be run before the "seen"
    # state of files is altered.
    # This test is materially different in the API & API Proxy versions.
    @qrexec_datasaver
    def test_download_submission(self):
        s = self.api.get_all_submissions()[0]

        assert not s.is_read

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
        assert not s.is_read

        # Let us remove the temporary directory
        shutil.rmtree(tmpdir)

    @qrexec_datasaver
    def test_seen(self):
        super().seen()

    @qrexec_datasaver
    def test_get_sources(self):
        super().get_sources()

    @qrexec_datasaver
    def test_star_add_remove(self):
        super().star_add_remove()

    @qrexec_datasaver
    def test_get_single_source(self):
        super().get_single_source()

    @qrexec_datasaver
    def test_get_single_source_from_string(self):
        super().get_single_source(from_string=True)

    @qrexec_datasaver
    def test_failed_single_source(self):
        super().failed_single_source()

    @qrexec_datasaver
    def test_get_submissions(self):
        super().get_submissions()

    @qrexec_datasaver
    def test_get_submission(self):
        super().get_submission()

    @qrexec_datasaver
    def test_get_submission_from_string(self):
        super().get_submission(from_string=True)

    @qrexec_datasaver
    def test_get_wrong_submissions(self):
        super().get_wrong_submissions()

    @qrexec_datasaver
    def test_get_all_submissions(self):
        super().get_all_submissions()

    @qrexec_datasaver
    def test_flag_source(self):
        super().flag_source()

    @qrexec_datasaver
    def test_get_current_user(self):
        super().get_current_user()

    @qrexec_datasaver
    def test_get_users(self):
        super().get_users()

    @qrexec_datasaver
    def test_error_unencrypted_reply(self):
        super().error_unencrypted_reply()

    @qrexec_datasaver
    def test_get_replies_from_source(self):
        super().get_replies_from_source()

    @qrexec_datasaver
    def test_get_reply_from_source(self):
        super().get_reply_from_source()

    @qrexec_datasaver
    def test_get_all_replies(self):
        super().get_all_replies()

    @qrexec_datasaver
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

    # ORDER MATTERS: The following tests add or delete data, and should
    # not be run before other tests which may rely on the original fixture
    # state.

    @qrexec_datasaver
    def test_reply_source(self):
        super().reply_source()

    @qrexec_datasaver
    def test_reply_source_with_uuid(self):
        super().reply_source_with_uuid()

    @qrexec_datasaver
    def test_delete_source(self):
        super().delete_source()

    @qrexec_datasaver
    def test_delete_source_from_string(self):
        super().delete_source(from_string=True)

    @qrexec_datasaver
    def test_delete_submission(self):
        super().delete_submission()

    @qrexec_datasaver
    def test_delete_submission_from_string(self):
        super().delete_submission(from_string=True)

    @qrexec_datasaver
    def test_delete_reply(self):
        super().delete_reply()

    @qrexec_datasaver
    def test_logout(self):
        r = self.api.logout()
        assert r


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
