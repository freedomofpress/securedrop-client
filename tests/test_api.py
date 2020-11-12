import hashlib
import shutil
import tempfile
import time

import pyotp
import pytest
import vcr
from requests.exceptions import ConnectTimeout, ReadTimeout

from sdclientapi import API, RequestTimeoutError
from sdclientapi.sdlocalobjects import AuthError, Reply, Submission
from test_shared import TestShared

NUM_REPLIES_PER_SOURCE = 2


class TestAPI(TestShared):
    """
    Note that TestShared contains most of the test code, which is shared between
    API and API Proxy tests.
    """

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
        super().api_auth()

    @vcr.use_cassette("data/test-seen.yml")
    def test_seen(self):
        super().seen()

    @vcr.use_cassette("data/test-get-sources.yml")
    def test_get_sources(self):
        super().get_sources()

    @vcr.use_cassette("data/test-star-add-remove.yml")
    def test_star_add_remove(self):
        super().star_add_remove()

    @vcr.use_cassette("data/test-get-single-source.yml")
    def test_get_single_source(self):
        super().get_single_source()

    @vcr.use_cassette("data/test-get-single-source.yml")
    def test_get_single_source_from_string(self):
        super().get_single_source(from_string=True)

    @vcr.use_cassette("data/test-failed-single-source.yml")
    def test_failed_single_source(self):
        super().failed_single_source()

    @vcr.use_cassette("data/test-get-submissions.yml")
    def test_get_submissions(self):
        super().get_submissions()

    @vcr.use_cassette("data/test-get-submission.yml")
    def test_get_submission(self):
        super().get_submission()

    @vcr.use_cassette("data/test-get-submission.yml")
    def test_get_submission_from_string(self):
        super().get_submission(from_string=True)

    @vcr.use_cassette("data/test-get-wrong-submissions.yml")
    def test_get_wrong_submissions(self):
        super().get_wrong_submissions()

    @vcr.use_cassette("data/test-get-all-submissions.yml")
    def test_get_all_submissions(self):
        super().get_all_submissions()

    @vcr.use_cassette("data/test-flag-source.yml")
    def test_flag_source(self):
        super().flag_source()

    @vcr.use_cassette("data/test-delete-source.yml")
    def test_delete_source(self):
        super().delete_source()

    @vcr.use_cassette("data/test-delete-source.yml")
    def test_delete_source_from_string(self):
        super().delete_source(from_string=True)

    @vcr.use_cassette("data/test-delete-submission.yml")
    def test_delete_submission(self):
        super().delete_submission()

    @vcr.use_cassette("data/test-delete-submission-from-string.yml")
    def test_delete_submission_from_string(self):
        super().delete_submission(from_string=True)

    @vcr.use_cassette("data/test-get-current-user.yml")
    def test_get_current_user(self):
        super().get_current_user()

    @vcr.use_cassette("data/test-get-users.yml")
    def test_get_users(self):
        super().get_users()

    @vcr.use_cassette("data/test-error-unencrypted-reply.yml")
    def test_error_unencrypted_reply(self):
        super().error_unencrypted_reply()

    @vcr.use_cassette("data/test-reply-source.yml")
    def test_reply_source(self):
        super().reply_source()

    @vcr.use_cassette("data/test-reply-source-with-uuid.yml")
    def test_reply_source_with_uuid(self):
        super().reply_source_with_uuid()

    # This test is materially different in the API & API Proxy versions.
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
        super().get_replies_from_source()

    @vcr.use_cassette("data/test-get-reply-from-source.yml")
    def test_get_reply_from_source(self):
        super().get_reply_from_source()

    @vcr.use_cassette("data/test-get-all-replies.yml")
    def test_get_all_replies(self):
        super().get_all_replies()

    # This test is materially different in the API & API Proxy versions.
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
        super().delete_reply()

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
