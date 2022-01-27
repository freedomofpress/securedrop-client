import os

import pytest

from securedrop_client.api_jobs.base import ApiInaccessibleError
from securedrop_client.api_jobs.sync import MetadataSyncJob
from securedrop_client.db import User
from tests import factory

with open(os.path.join(os.path.dirname(__file__), "..", "files", "test-key.gpg.pub.asc")) as f:
    PUB_KEY = f.read()


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


def test_MetadataSyncJob_raises_when_current_user_no_longer_exists(
    mocker, homedir, session, session_maker
):
    api_client = mocker.patch("securedrop_client.logic.sdclientapi.API")
    mocker.patch.object(api_client, "get_current_user", return_value=None)

    job = MetadataSyncJob(homedir)
    with pytest.raises(ApiInaccessibleError):
        job.call_api(api_client, session)


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
