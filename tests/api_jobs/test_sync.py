import os
import unittest
from collections import namedtuple

from securedrop_client import state
from securedrop_client.api_jobs.sync import MetadataSyncJob, _update_state
from securedrop_client.db import User
from tests import factory

with open(os.path.join(os.path.dirname(__file__), "..", "files", "test-key.gpg.pub.asc")) as f:
    PUB_KEY = f.read()

Source = namedtuple("Source", ["uuid"])
Submission = namedtuple("Submission", ["uuid", "source_uuid", "is_file", "is_downloaded"])
File = namedtuple("File", ["is_downloaded"])


class TestUpdateState(unittest.TestCase):
    def setUp(self):
        self._state = state.State()
        self._sources = []
        self._submissions = []

    def test_handles_missing_files_gracefully(self):
        self._sources = [
            Source(uuid="3"),
            Source(uuid="4"),
        ]
        self._submissions = [
            Submission(uuid="6", source_uuid="3", is_file=lambda: True, is_downloaded=True),
            Submission(uuid="7", source_uuid="4", is_file=lambda: True, is_downloaded=True),
            Submission(uuid="8", source_uuid="3", is_file=lambda: False, is_downloaded=True),
            Submission(uuid="9", source_uuid="3", is_file=lambda: True, is_downloaded=False),
        ]

        _update_state(self._state, self._submissions)
        assert self._state.file("6")
        assert self._state.file("7")
        assert not self._state.file("8")
        assert self._state.file("9")


def test_MetadataSyncJob_creates_new_user(mocker, homedir, session, session_maker):
    api_client = mocker.patch("securedrop_client.logic.sdclientapi.API")
    remote_user = factory.RemoteUser()
    api_client.get_users = mocker.MagicMock(return_value=[remote_user])

    job = MetadataSyncJob(homedir)
    job.call_api(api_client, session)

    local_user = session.query(User).filter_by(uuid=remote_user.uuid).one_or_none()
    assert local_user


def test_MetadataSyncJob_creates_new_special_deleted_user(mocker, homedir, session, session_maker):
    api_client = mocker.patch("securedrop_client.logic.sdclientapi.API")
    remote_user = factory.RemoteUser(username="deleted")
    api_client.get_users = mocker.MagicMock(return_value=[remote_user])

    job = MetadataSyncJob(homedir)
    job.call_api(api_client, session)

    local_user = session.query(User).filter_by(uuid=remote_user.uuid).one_or_none()
    assert local_user.deleted


def test_MetadataSyncJob_updates_application_state(mocker, homedir, session, session_maker):
    api_client = mocker.patch("securedrop_client.logic.sdclientapi.API")
    some_file = factory.RemoteFile()
    some_message = factory.RemoteMessage()
    another_file = factory.RemoteFile()
    submissions = [some_file, some_message, another_file]
    mocker.patch(
        "securedrop_client.api_jobs.sync.get_remote_data", return_value=([], submissions, [])
    )

    app_state = state.State()
    state_updater = mocker.patch("securedrop_client.api_jobs.sync._update_state")

    exising_user = factory.User(uuid="abc123-ima-uuid")
    session.add(exising_user)

    job = MetadataSyncJob(homedir, app_state)
    job.call_api(api_client, session)

    state_updater.assert_called_once_with(app_state, submissions)


def test_MetadataSyncJob_updates_existing_user(mocker, homedir, session, session_maker):
    api_client = mocker.patch("securedrop_client.logic.sdclientapi.API")
    remote_user = factory.RemoteUser(
        uuid="abc123-ima-uuid",
        username="new-username",
        first_name="NewFirstName",
        last_name="NewLastName",
    )
    api_client.get_users = mocker.MagicMock(return_value=[remote_user])

    exising_user = factory.User(uuid="abc123-ima-uuid")
    session.add(exising_user)

    job = MetadataSyncJob(homedir)
    job.call_api(api_client, session)

    assert exising_user.username == "new-username"
    assert exising_user.firstname == "NewFirstName"
    assert exising_user.lastname == "NewLastName"


def test_MetadataSyncJob_deletes_user(mocker, homedir, session, session_maker):
    api_client = mocker.patch("securedrop_client.logic.sdclientapi.API")
    api_client.get_users = mocker.MagicMock(return_value=[])

    user = factory.User()
    session.add(user)

    job = MetadataSyncJob(homedir)
    job.call_api(api_client, session)

    local_user = session.query(User).filter_by(uuid=user.uuid).one_or_none()
    assert not local_user


def test_MetadataSyncJob_success(mocker, homedir, session, session_maker):
    job = MetadataSyncJob(homedir)

    mock_source = factory.RemoteSource(
        key={"type": "PGP", "public": PUB_KEY, "fingerprint": "123456ABC"}
    )

    mock_get_remote_data = mocker.patch(
        "securedrop_client.api_jobs.sync.get_remote_data", return_value=([mock_source], [], [])
    )

    user = factory.User(uuid="mock1", username="mock1", firstname="mock1", lastname="mock1")
    session.add(user)

    api_client = mocker.patch("securedrop_client.logic.sdclientapi.API")

    user = {"uuid": "mock1", "username": "mock1", "first_name": "mock1", "last_name": "mock1"}
    mocker.patch.object(api_client, "get_current_user", return_value=user)

    job.call_api(api_client, session)

    assert mock_get_remote_data.call_count == 1


def test_MetadataSyncJob_success_current_user_name_change(mocker, homedir, session, session_maker):
    job = MetadataSyncJob(homedir)

    mock_source = factory.RemoteSource(
        key={"type": "PGP", "public": PUB_KEY, "fingerprint": "123456ABC"}
    )

    mock_get_remote_data = mocker.patch(
        "securedrop_client.api_jobs.sync.get_remote_data", return_value=([mock_source], [], [])
    )

    user = factory.User(uuid="mock1", username="mock1", firstname="mock1", lastname="mock1")
    session.add(user)

    api_client = mocker.patch("securedrop_client.logic.sdclientapi.API")

    user = {"uuid": "mock2", "username": "mock2", "first_name": "mock2", "last_name": "mock2"}
    mocker.patch.object(api_client, "get_current_user", return_value=user)

    job.call_api(api_client, session)

    assert mock_get_remote_data.call_count == 1


def test_MetadataSyncJob_success_with_missing_key(mocker, homedir, session, session_maker):
    """
    Check that we can gracefully handle missing source keys.
    """
    job = MetadataSyncJob(homedir)

    mock_source = factory.RemoteSource(key={"type": "PGP", "public": "", "fingerprint": ""})

    mock_get_remote_data = mocker.patch(
        "securedrop_client.api_jobs.sync.get_remote_data", return_value=([mock_source], [], [])
    )

    api_client = mocker.MagicMock()
    api_client.default_request_timeout = mocker.MagicMock()

    job.call_api(api_client, session)

    assert mock_get_remote_data.call_count == 1
