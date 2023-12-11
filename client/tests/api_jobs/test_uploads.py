import datetime

import pytest
import sdclientapi

from securedrop_client import db
from securedrop_client.api_jobs.uploads import (
    SendReplyJob,
    SendReplyJobError,
    SendReplyJobTimeoutError,
)
from securedrop_client.crypto import CryptoError, GpgHelper
from tests import factory


def test_SendReplyJobTimeoutError():
    error = SendReplyJobTimeoutError("mock_message", "mock_reply_id")
    assert str(error) == "mock_message"


def test_send_reply_success(homedir, mocker, session, session_maker, reply_status_codes):
    """
    Check that the "happy path" of encrypting a message and sending it to the
    server behaves as expected.
    """
    source = factory.Source()
    session.add(source)
    msg_uuid = "xyz456"
    draft_reply = factory.DraftReply(uuid=msg_uuid)
    session.add(draft_reply)
    session.commit()

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)

    api_client = mocker.MagicMock()
    api_client.token_journalist_uuid = "journalist ID sending the reply"
    user = factory.User(uuid="journalist ID sending the reply")
    session.add(user)
    session.commit()

    encrypted_reply = "s3kr1t m3ss1dg3"
    mock_encrypt = mocker.patch.object(gpg, "encrypt_to_source", return_value=encrypted_reply)
    msg = "wat"

    mock_reply_response = sdclientapi.Reply(uuid=msg_uuid, filename="5-dummy-reply")
    api_client.reply_source = mocker.MagicMock()
    api_client.reply_source.return_value = mock_reply_response

    mock_sdk_source = mocker.Mock()
    mock_source_init = mocker.patch(
        "securedrop_client.logic.sdclientapi.Source", return_value=mock_sdk_source
    )

    job = SendReplyJob(source.uuid, msg_uuid, msg, gpg)

    job.call_api(api_client, session)

    # ensure message gets encrypted
    mock_encrypt.assert_called_once_with(source.uuid, msg)
    mock_source_init.assert_called_once_with(uuid=source.uuid)

    # assert reply got added to db
    reply = session.query(db.Reply).filter_by(uuid=msg_uuid).one()
    assert reply.journalist_id == user.id


def test_send_reply_fails_when_no_user(homedir, mocker, session, session_maker, reply_status_codes):
    """
    Check that an exception is raised when trying to send a reply from a journalist who doesn't
    exist in the local db.
    """
    source = factory.Source()
    session.add(source)
    mocker.patch("securedrop_client.logic.sdclientapi.Source", return_value=mocker.Mock())

    draft_reply = factory.DraftReply(uuid="mock_reply_uuid")
    session.add(draft_reply)
    session.commit()

    api_client = mocker.MagicMock()
    api_client.token_journalist_uuid = "UUID for journalist without an account"

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    mocker.patch.object(gpg, "encrypt_to_source", return_value="s3kr1t m3ss1dg3")

    job = SendReplyJob(source.uuid, "mock_reply_uuid", "mock_message", gpg)
    error = "Sender of reply {} has been deleted".format("mock_reply_uuid")
    with pytest.raises(SendReplyJobError, match=error):
        job.call_api(api_client, session)


def test_drafts_ordering(homedir, mocker, session, session_maker, reply_status_codes):
    """
    Check that if a reply is successful, drafts sent before and after
    continue to appear in the same order.
    """
    initial_interaction_count = 1
    source_uuid = "foo"
    source = factory.Source(uuid=source_uuid, interaction_count=initial_interaction_count)
    session.add(source)
    msg_uuid = "xyz456"

    draft_reply = factory.DraftReply(uuid=msg_uuid, file_counter=1)
    session.add(draft_reply)
    session.commit()

    failed_status = (
        session.query(db.ReplySendStatus).filter_by(name=db.ReplySendStatusCodes.FAILED.value).one()
    )

    # Failed Draft reply from the previous session.
    draft_reply_before_failed = factory.DraftReply(
        timestamp=draft_reply.timestamp - datetime.timedelta(minutes=5),
        source_id=source.id,
        file_counter=draft_reply.file_counter,
        uuid="foo",
        send_status=failed_status,
    )
    session.add(draft_reply_before_failed)

    # Draft reply from the previous queue job.
    draft_reply_before = factory.DraftReply(
        timestamp=draft_reply.timestamp - datetime.timedelta(minutes=1),
        source_id=source.id,
        file_counter=draft_reply.file_counter,
        uuid="bar",
    )
    session.add(draft_reply_before)

    # Draft reply that the queue will operate on next.
    draft_reply_after = factory.DraftReply(
        timestamp=draft_reply.timestamp + datetime.timedelta(minutes=1),
        source_id=source.id,
        file_counter=draft_reply.file_counter,
        uuid="baz",
    )

    session.add(draft_reply_after)
    session.commit()

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)

    api_client = mocker.MagicMock()
    api_client.token_journalist_uuid = "journalist ID sending the reply"
    user = factory.User(uuid="journalist ID sending the reply")
    session.add(user)
    session.commit()

    encrypted_reply = "s3kr1t m3ss1dg3"
    mock_encrypt = mocker.patch.object(gpg, "encrypt_to_source", return_value=encrypted_reply)
    msg = "wat"

    mock_reply_response = sdclientapi.Reply(uuid=msg_uuid, filename="2-dummy-reply")
    api_client.reply_source = mocker.MagicMock()
    api_client.reply_source.return_value = mock_reply_response

    mock_sdk_source = mocker.Mock()
    mock_source_init = mocker.patch(
        "securedrop_client.logic.sdclientapi.Source", return_value=mock_sdk_source
    )

    job = SendReplyJob(source.uuid, msg_uuid, msg, gpg)

    job.call_api(api_client, session)

    # ensure message gets encrypted
    mock_encrypt.assert_called_once_with(source.uuid, msg)
    mock_source_init.assert_called_once_with(uuid=source.uuid)

    # assert reply got added to db
    reply = session.query(db.Reply).filter_by(uuid=msg_uuid).one()
    assert reply.journalist_id == user.id

    # We use the file_counter on each Reply, Message, File, and DraftReply
    # object to order the conversation view. We expect a unique file_counter
    # for Reply, Message, and File objects since they are retrieved from
    # the server.
    # For DraftReply, we don't have that unique constraint, and we instead expect
    # the file_counter to be the interaction_count at the time of send.
    # If we do not update the interaction_count after each successful reply send,
    # future drafts will have an interaction_count that is too low, leading
    # to incorrectly ordered drafts until a metadata sync completes (the metadata
    # sync is the place where the source object is updated from the server).
    source = session.query(db.Source).filter_by(uuid=source_uuid).one()
    assert source.interaction_count == initial_interaction_count + 1

    # Check the ordering displayed to the user.
    # We push Draft replies in the Pending state to the end of the conversation thread;
    # failed replies remain threaded normally
    assert source.collection[0] == draft_reply_before_failed
    assert source.collection[1] == reply
    assert source.collection[2] == draft_reply_before
    assert source.collection[3] == draft_reply_after


def test_send_reply_failure_gpg_error(homedir, mocker, session, session_maker, reply_status_codes):
    """
    Check that if gpg fails when sending a message, we do not call the API, and ensure that
    SendReplyJobError is raised when there is a CryptoError so we can handle it in
    ApiJob._do_call_api.
    """
    source = factory.Source()
    session.add(source)
    msg_uuid = "xyz456"
    draft_reply = factory.DraftReply(uuid=msg_uuid)
    session.add(draft_reply)
    session.commit()

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)

    api_client = mocker.MagicMock()
    api_client.token_journalist_uuid = "journalist ID sending the reply"
    user = factory.User(uuid="journalist ID sending the reply")
    session.add(user)
    session.commit()

    mock_encrypt = mocker.patch.object(gpg, "encrypt_to_source", side_effect=CryptoError)
    msg = "wat"

    mock_reply_response = sdclientapi.Reply(uuid=msg_uuid, filename="5-dummy-reply")
    api_client.reply_source = mocker.MagicMock()
    api_client.reply_source.return_value = mock_reply_response

    mock_sdk_source = mocker.Mock()
    mock_source_init = mocker.patch(
        "securedrop_client.logic.sdclientapi.Source", return_value=mock_sdk_source
    )

    job = SendReplyJob(source.uuid, msg_uuid, msg, gpg)

    with pytest.raises(SendReplyJobError):
        job.call_api(api_client, session)

    # Ensure we attempted to encrypt the message
    mock_encrypt.assert_called_once_with(source.uuid, msg)
    assert mock_source_init.call_count == 0

    # Ensure reply did not get added to db
    replies = session.query(db.Reply).filter_by(uuid=msg_uuid).all()
    assert len(replies) == 0

    # Ensure that the draft reply is still in the db
    drafts = session.query(db.DraftReply).filter_by(uuid=msg_uuid).all()
    assert len(drafts) == 1


def test_send_reply_sql_exception_during_failure(
    homedir, mocker, session, session_maker, reply_status_codes
):
    """
    Check that we do not raise an unhandled exception when we set the draft reply
    status to failed in the except block if there is a SQL exception.
    """
    source = factory.Source()
    session.add(source)

    # Note that we do not add a DraftReply. An exception will occur when we try
    # to set the reply status to 'FAILED' for a nonexistent reply, which we
    # expect to be handled.

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = SendReplyJob(source.uuid, "mock_reply_uuid", "mock_message", gpg)

    # This should not raise an exception
    job._set_status_to_failed(session)


def test_send_reply_unexpected_exception_during_failure(
    homedir, mocker, session, session_maker, reply_status_codes
):
    """
    Check that we do not raise an unhandled exception when we set the draft reply
    status to failed in the except block if there is an unexpected exception.
    """
    source = factory.Source()
    session.add(source)
    draft_reply = factory.DraftReply(uuid="mock_reply_uuid")
    session.add(draft_reply)
    session.commit()

    # session.commit() is called when we try to set the status to failed.
    session.commit = mocker.MagicMock(side_effect=Exception("BOOM"))

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = SendReplyJob(source.uuid, "mock_reply_uuid", "mock_message", gpg)

    # This should not raise an exception
    job._set_status_to_failed(session)


def test_send_reply_failure_unknown_error(
    homedir, mocker, session, session_maker, reply_status_codes
):
    """
    Check that if the SendReplyJob api call fails when sending a message that SendReplyJobError
    is raised and the reply is not added to the local database.
    """
    source = factory.Source()
    session.add(source)
    draft_reply = factory.DraftReply(uuid="mock_reply_uuid")
    session.add(draft_reply)
    session.commit()

    api_client = mocker.MagicMock()
    api_client.token_journalist_uuid = "journalist ID sending the reply"
    user = factory.User(uuid="journalist ID sending the reply")
    session.add(user)
    session.commit()

    mocker.patch.object(api_client, "reply_source", side_effect=Exception)
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    encrypt_fn = mocker.patch.object(gpg, "encrypt_to_source")
    job = SendReplyJob(source.uuid, "mock_reply_uuid", "mock_message", gpg)

    with pytest.raises(Exception):
        job.call_api(api_client, session)

    encrypt_fn.assert_called_once_with(source.uuid, "mock_message")
    replies = session.query(db.Reply).filter_by(uuid="mock_reply_uuid").all()
    assert len(replies) == 0

    # Ensure that the draft reply is still in the db
    drafts = session.query(db.DraftReply).filter_by(uuid="mock_reply_uuid").all()
    assert len(drafts) == 1


@pytest.mark.parametrize(
    "exception", [sdclientapi.RequestTimeoutError, sdclientapi.ServerConnectionError]
)
def test_send_reply_failure_timeout_error(
    homedir, mocker, session, session_maker, reply_status_codes, exception
):
    """
    Check that if the SendReplyJob api call fails because of a RequestTimeoutError or
    ServerConnectionError that a SendReplyJobTimeoutError is raised.
    """
    source = factory.Source()
    session.add(source)
    draft_reply = factory.DraftReply(uuid="mock_reply_uuid")
    session.add(draft_reply)
    session.commit()

    api_client = mocker.MagicMock()
    api_client.token_journalist_uuid = "journalist ID sending the reply"
    user = factory.User(uuid="journalist ID sending the reply")
    session.add(user)
    session.commit()

    mocker.patch.object(api_client, "reply_source", side_effect=exception)
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    encrypt_fn = mocker.patch.object(gpg, "encrypt_to_source")
    job = SendReplyJob(source.uuid, "mock_reply_uuid", "mock_message", gpg)

    with pytest.raises(SendReplyJobTimeoutError):
        job.call_api(api_client, session)

    encrypt_fn.assert_called_once_with(source.uuid, "mock_message")
    replies = session.query(db.Reply).filter_by(uuid="mock_reply_uuid").all()
    assert len(replies) == 0

    # Ensure that the draft reply is still in the db
    drafts = session.query(db.DraftReply).filter_by(uuid="mock_reply_uuid").all()
    assert len(drafts) == 1


def test_send_reply_failure_when_repr_is_none(
    homedir, mocker, session, session_maker, reply_status_codes
):
    """
    Check that the SendReplyJob api call results in a SendReplyJobError and nothing else, e.g.
    no TypeError, when an api call results in an exception that returns None for __repr__
    (regression test).
    """

    class MockException(Exception):
        def __repr__(self):
            return None

    source = factory.Source(uuid="mock_reply_uuid")
    session.add(source)
    draft_reply = factory.DraftReply(uuid="mock_reply_uuid")
    session.add(draft_reply)
    session.commit()

    api_client = mocker.MagicMock()
    api_client.token_journalist_uuid = "journalist ID sending the reply"
    user = factory.User(uuid="journalist ID sending the reply")
    session.add(user)
    session.commit()

    mocker.patch.object(api_client, "reply_source", side_effect=MockException("mock"))
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    encrypt_fn = mocker.patch.object(gpg, "encrypt_to_source")
    job = SendReplyJob(source.uuid, "mock_reply_uuid", "mock_message", gpg)

    error = "Failed to send reply mock_reply_uuid for source {} due to Exception: mock".format(
        source.uuid
    )
    with pytest.raises(SendReplyJobError, match=error):
        job.call_api(api_client, session)

    encrypt_fn.assert_called_once_with(source.uuid, "mock_message")
    replies = session.query(db.Reply).filter_by(uuid="mock_reply_uuid").all()
    assert len(replies) == 0

    # Ensure that the draft reply is still in the db
    drafts = session.query(db.DraftReply).filter_by(uuid="mock_reply_uuid").all()
    assert len(drafts) == 1


def test_reply_already_sent(homedir, mocker, session, session_maker, reply_status_codes):
    """
    Check that if a reply is already sent then we return the reply id.
    """
    source = factory.Source()
    session.add(source)
    reply = factory.Reply(source=source)
    session.add(reply)
    session.commit()

    job = SendReplyJob("mock_source_id", reply.uuid, "mock reply message", mocker.MagicMock())
    reply_uuid = job.call_api(mocker.MagicMock(), session)

    assert reply.uuid == reply_uuid


def test_reply_deleted_locally(homedir, mocker, session, session_maker, reply_status_codes):
    """
    Check that if a draft does not exist then we raise a SendReplyJobException so that the job
    is skipped.
    """
    job = SendReplyJob("mock_source_id", "mock_uuid", "mock reply message", mocker.MagicMock())
    error = "Failed to send reply mock_uuid for source mock_source_id due to Exception"
    with pytest.raises(SendReplyJobError, match=error):
        job.call_api(mocker.MagicMock(), session)


def test_source_deleted_locally(homedir, mocker, session, session_maker, reply_status_codes):
    """
    Check that if a source has been deleted then raise a SendReplyJobException so that the job
    is skipped.
    """
    draft = factory.DraftReply()
    session.add(draft)
    session.commit()

    job = SendReplyJob("nonexistent_id", draft.uuid, "mock reply message", mocker.MagicMock())
    error = "Failed to send reply {} for source {} due to Exception".format(
        draft.uuid, "nonexistent_id"
    )
    with pytest.raises(SendReplyJobError, match=error):
        job.call_api(mocker.MagicMock(), session)
