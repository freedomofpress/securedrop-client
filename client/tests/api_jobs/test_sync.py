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

TIMEOUT_OVERRIDE = 600  # sec


class TestUpdateState(unittest.TestCase):
    def setUp(self):
        self._state = state.State()
        self._sources = []
        self._submissions = []

    def test_handles_missing_files_gracefully(self):
        self._sources = [Source(uuid="3"), Source(uuid="4")]
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


def test_MetadataSyncJob_has_default_timeout(mocker, homedir, session, session_maker):
    api_client = mocker.patch("securedrop_client.logic.sdclientapi.API")
    remote_user = factory.RemoteUser()
    api_client.get_users = mocker.MagicMock(return_value=[remote_user])

    job = MetadataSyncJob(homedir)
    job.call_api(api_client, session)
    assert api_client.default_request_timeout == job.DEFAULT_REQUEST_TIMEOUT


def test_MetadataSyncJob_takes_overridden_timeout(mocker, homedir, session, session_maker):
    api_client = mocker.patch("securedrop_client.logic.sdclientapi.API")
    remote_user = factory.RemoteUser()
    api_client.get_users = mocker.MagicMock(return_value=[remote_user])

    os.environ["SDEXTENDEDTIMEOUT"] = str(TIMEOUT_OVERRIDE)  # environment value must be string

    job = MetadataSyncJob(homedir)
    job.call_api(api_client, session)
    assert api_client.default_request_timeout == TIMEOUT_OVERRIDE

    # Don't pollute the environment for subsequent/out-of-order tests.
    del os.environ["SDEXTENDEDTIMEOUT"]


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

    existing_user = factory.User(uuid="abc123-ima-uuid")
    session.add(existing_user)

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

    existing_user = factory.User(uuid="abc123-ima-uuid")
    session.add(existing_user)

    job = MetadataSyncJob(homedir)
    job.call_api(api_client, session)

    assert existing_user.username == "new-username"
    assert existing_user.firstname == "NewFirstName"
    assert existing_user.lastname == "NewLastName"


def test_MetadataSyncJob_deletes_user(mocker, homedir, session, session_maker):
    api_client = mocker.patch("securedrop_client.logic.sdclientapi.API")
    api_client.get_users = mocker.MagicMock(return_value=[])

    user = factory.User()
    session.add(user)

    job = MetadataSyncJob(homedir)
    job.call_api(api_client, session)

    local_user = session.query(User).filter_by(uuid=user.uuid).one_or_none()
    assert not local_user


def test_MetadataSyncJob_does_not_delete_reserved_deleted_user(mocker, homedir, session):
    """
    Ensure that we do not delete the local "deleted" user account unless a "deleted" user account
    exists on the server that we can replace it with.

    This test is to ensure that we support an edge case that can occur on a pre-2.2.0 server
    (before the server added support for creating an actual deleted user account).
    """
    api_client = mocker.patch("securedrop_client.logic.sdclientapi.API")
    api_client.get_users = mocker.MagicMock(return_value=[])

    reserved_deleted_user = factory.User(username="deleted")
    session.add(reserved_deleted_user)

    job = MetadataSyncJob(homedir)
    job.call_api(api_client, session)

    assert session.query(User).filter_by(username="deleted").one_or_none()


def test_MetadataSyncJob_reassociates_draftreplies_to_new_account_before_deleting_user(
    mocker, homedir, session
):
    """
    Ensure that any draft replies sent by a user that is about to be deleted are re-associated
    to a new "deleted" user account that exists on the server.
    """
    user_to_delete_with_drafts = factory.User()
    session.add(user_to_delete_with_drafts)
    session.commit()
    draftreply = factory.DraftReply(journalist_id=user_to_delete_with_drafts.id)
    session.add(draftreply)
    session.commit()

    remote_reserved_deleted_user = factory.RemoteUser(username="deleted")
    # Set up get_users so that `user_to_delete_with_drafts` will be deleted and
    # `remote_reserved_deleted_user` will be created since it exists on the server
    api_client = mocker.patch("securedrop_client.logic.sdclientapi.API")
    api_client.get_users = mocker.MagicMock(return_value=[remote_reserved_deleted_user])

    job = MetadataSyncJob(homedir)
    job.call_api(api_client, session)

    # Ensure the account was deleted
    deleted_user = session.query(User).filter_by(uuid=user_to_delete_with_drafts.uuid).one_or_none()
    assert not deleted_user
    # Ensure the "deleted" user account that exists on the server was created locally
    reserved_deleted_user = session.query(User).filter_by(username="deleted").one_or_none()
    assert reserved_deleted_user
    assert reserved_deleted_user.uuid == remote_reserved_deleted_user.uuid
    # Ensure draft replies are reassociated
    assert draftreply.journalist_id == reserved_deleted_user.id


def test_MetadataSyncJob_reassociates_draftreplies_to_existing_account_before_deleting_user(
    mocker, homedir, session
):
    """
    Ensure that any draft replies sent by a user that is about to be deleted are re-associated
    to an existing "deleted" user account.
    """
    user_to_delete_with_drafts = factory.User()
    session.add(user_to_delete_with_drafts)
    session.commit()
    draftreply = factory.DraftReply(journalist_id=user_to_delete_with_drafts.id)
    session.add(draftreply)
    session.commit()

    local_reserved_deleted_user = factory.User(username="deleted")
    session.add(local_reserved_deleted_user)
    session.commit()

    remote_reserved_deleted_user = factory.RemoteUser(
        username="deleted", uuid=local_reserved_deleted_user.uuid
    )
    # Set up get_users so that `user_to_delete_with_drafts` will be deleted and
    # `remote_reserved_deleted_user` will replace `local_reserved_deleted_user`
    api_client = mocker.patch("securedrop_client.logic.sdclientapi.API")
    api_client.get_users = mocker.MagicMock(return_value=[remote_reserved_deleted_user])

    job = MetadataSyncJob(homedir)
    job.call_api(api_client, session)

    # Ensure the account was deleted
    deleted_user = session.query(User).filter_by(uuid=user_to_delete_with_drafts.uuid).one_or_none()
    assert not deleted_user
    # Ensure the "deleted" user account still exists
    reserved_deleted_user = session.query(User).filter_by(username="deleted").one_or_none()
    assert reserved_deleted_user
    assert reserved_deleted_user.uuid == local_reserved_deleted_user.uuid
    # Ensure draft replies are reassociated
    assert draftreply.journalist_id == reserved_deleted_user.id


def test_MetadataSyncJob_reassociates_draftreplies_to_new_local_account_before_deleting_user(
    mocker, homedir, session
):
    """
    Ensure that any draft replies, sent by a user that is about to be deleted, are re-associated
    to a new "deleted" user account that only exists locally.

    This test is to ensure that we support an edge case that can occur on a pre-2.2.0 server
    (before the server added support for creating an actual deleted user account).
    """
    user_to_delete_with_drafts = factory.User()
    session.add(user_to_delete_with_drafts)
    session.commit()

    draftreply = factory.DraftReply(journalist_id=user_to_delete_with_drafts.id)
    session.add(draftreply)
    # Set up get_users so that `user_to_delete_with_drafts` will be deleted
    api_client = mocker.patch("securedrop_client.logic.sdclientapi.API")
    api_client.get_users = mocker.MagicMock(return_value=[])

    job = MetadataSyncJob(homedir)
    job.call_api(api_client, session)

    # Ensure the account was deleted
    deleted_user = session.query(User).filter_by(uuid=user_to_delete_with_drafts.uuid).one_or_none()
    assert not deleted_user
    # Ensure the "deleted" user account exists
    reserved_deleted_user = session.query(User).filter_by(username="deleted").one_or_none()
    assert reserved_deleted_user
    # Ensure draft replies are reassociated
    assert draftreply.journalist_id == reserved_deleted_user.id


def test_MetadataSyncJob_replaces_reserved_deleted_user_account(mocker, homedir, session):
    """
    Ensure that we delete the local "deleted" user account if it is being replaced by a new account
    from the server and that any draft replies are re-associated appropriately.

    This test is to ensure that we support an edge case that can occur on a pre-2.2.0 server
    (before the server added support for creating an actual deleted user account).
    """
    local_reserved_deleted_user = factory.User(username="deleted")
    session.add(local_reserved_deleted_user)
    session.commit()
    draftreply = factory.DraftReply(journalist_id=local_reserved_deleted_user.id)
    session.add(draftreply)
    session.commit()

    remote_reserved_deleted_user = factory.RemoteUser(username="deleted")
    # Set up get_users so that `user_to_delete_with_drafts` will be deleted and
    # `remote_reserved_deleted_user` will replace `local_reserved_deleted_user`
    api_client = mocker.patch("securedrop_client.logic.sdclientapi.API")
    api_client.get_users = mocker.MagicMock(return_value=[remote_reserved_deleted_user])

    job = MetadataSyncJob(homedir)
    job.call_api(api_client, session)

    # Ensure `remote_reserved_deleted_user` replaced `local_reserved_deleted_user` and that the
    # draft reply was reassociated to the new "deleted" user account.
    reserved_deleted_user = session.query(User).filter_by(username="deleted").one_or_none()
    assert reserved_deleted_user
    assert reserved_deleted_user.uuid == remote_reserved_deleted_user.uuid
    assert draftreply.journalist_id == reserved_deleted_user.id


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
