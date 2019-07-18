import pytest
import sdclientapi

from securedrop_client import db
from securedrop_client.api_jobs.uploads import SendReplyJob, SendReplyJobException
from securedrop_client.crypto import GpgHelper, CryptoError
from tests import factory


def test_send_reply_success(homedir, mocker, session, session_maker):
    '''
    Check that the "happy path" of encrypting a message and sending it to the
    server behaves as expected.
    '''
    source = factory.Source()
    session.add(source)
    session.commit()

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)

    api_client = mocker.MagicMock()
    api_client.token_journalist_uuid = 'journalist ID sending the reply'

    encrypted_reply = 's3kr1t m3ss1dg3'
    mock_encrypt = mocker.patch.object(gpg, 'encrypt_to_source', return_value=encrypted_reply)
    msg_uuid = 'xyz456'
    msg = 'wat'

    mock_reply_response = sdclientapi.Reply(uuid=msg_uuid, filename='5-dummy-reply')
    api_client.reply_source = mocker.MagicMock()
    api_client.reply_source.return_value = mock_reply_response

    mock_sdk_source = mocker.Mock()
    mock_source_init = mocker.patch('securedrop_client.logic.sdclientapi.Source',
                                    return_value=mock_sdk_source)

    job = SendReplyJob(
        source.uuid,
        msg_uuid,
        msg,
        gpg,
    )

    job.call_api(api_client, session)

    # ensure message gets encrypted
    mock_encrypt.assert_called_once_with(source.uuid, msg)
    mock_source_init.assert_called_once_with(uuid=source.uuid)

    # assert reply got added to db
    reply = session.query(db.Reply).filter_by(uuid=msg_uuid).one()
    assert reply.journalist_id == api_client.token_journalist_uuid


def test_send_reply_failure_gpg_error(homedir, mocker, session, session_maker):
    '''
    Check that if gpg fails when sending a message, we do not call the API, and ensure that
    SendReplyJobException is raised when there is a CryptoError so we can handle it in
    ApiJob._do_call_api.
    '''
    source = factory.Source()
    session.add(source)
    session.commit()

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)

    api_client = mocker.MagicMock()
    api_client.token_journalist_uuid = 'journalist ID sending the reply'

    mock_encrypt = mocker.patch.object(gpg, 'encrypt_to_source', side_effect=CryptoError)
    msg_uuid = 'xyz456'
    msg = 'wat'

    mock_reply_response = sdclientapi.Reply(uuid=msg_uuid, filename='5-dummy-reply')
    api_client.reply_source = mocker.MagicMock()
    api_client.reply_source.return_value = mock_reply_response

    mock_sdk_source = mocker.Mock()
    mock_source_init = mocker.patch('securedrop_client.logic.sdclientapi.Source',
                                    return_value=mock_sdk_source)

    job = SendReplyJob(
        source.uuid,
        msg_uuid,
        msg,
        gpg,
    )

    with pytest.raises(SendReplyJobException):
        job.call_api(api_client, session)

    # Ensure we attempted to encrypt the message
    mock_encrypt.assert_called_once_with(source.uuid, msg)
    assert mock_source_init.call_count == 0

    # Ensure reply did not get added to db
    replies = session.query(db.Reply).filter_by(uuid=msg_uuid).all()
    assert len(replies) == 0


def test_send_reply_failure_unknown_error(homedir, mocker, session, session_maker):
    '''
    Check that if the SendReplyJob api call fails when sending a message that SendReplyJobException
    is raised and the reply is not added to the local database.
    '''
    source = factory.Source()
    session.add(source)
    session.commit()
    api_client = mocker.MagicMock()
    mocker.patch.object(api_client, 'reply_source', side_effect=Exception)
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    encrypt_fn = mocker.patch.object(gpg, 'encrypt_to_source')
    job = SendReplyJob(source.uuid, 'mock_reply_uuid', 'mock_message', gpg)

    with pytest.raises(Exception):
        job.call_api(api_client, session)

    encrypt_fn.assert_called_once_with(source.uuid, 'mock_message')
    replies = session.query(db.Reply).filter_by(uuid='mock_reply_uuid').all()
    assert len(replies) == 0


def test_send_reply_failure_when_repr_is_none(homedir, mocker, session, session_maker):
    '''
    Check that the SendReplyJob api call results in a SendReplyJobException and nothing else, e.g.
    no TypeError, when an api call results in an exception that returns None for __repr__
    (regression test).
    '''
    class MockException(Exception):
        def __repr__(self):
            return None

    source = factory.Source(uuid='mock_reply_uuid')
    session.add(source)
    session.commit()
    api_client = mocker.MagicMock()
    mocker.patch.object(api_client, 'reply_source', side_effect=MockException('mock'))
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    encrypt_fn = mocker.patch.object(gpg, 'encrypt_to_source')
    job = SendReplyJob(source.uuid, 'mock_reply_uuid', 'mock_message', gpg)

    with pytest.raises(
            SendReplyJobException,
            match=r'Failed to send reply for source mock_reply_uuid due to Exception: mock'):
        job.call_api(api_client, session)

    encrypt_fn.assert_called_once_with(source.uuid, 'mock_message')
    replies = session.query(db.Reply).filter_by(uuid='mock_reply_uuid').all()
    assert len(replies) == 0
