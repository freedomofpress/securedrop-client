import pytest
import sdclientapi

from securedrop_client import db
from securedrop_client.api_jobs.uploads import SendReplyJob
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
    Check that if gpg fails when sending a message, we do not call the API.
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

    # Ensure that the CryptoError is raised so we can handle it in ApiJob._do_call_api
    with pytest.raises(CryptoError):
        job.call_api(api_client, session)

    # Ensure we attempted to encrypt the message
    mock_encrypt.assert_called_once_with(source.uuid, msg)
    assert mock_source_init.call_count == 0

    # Ensure reply did not get added to db
    replies = session.query(db.Reply).filter_by(uuid=msg_uuid).all()
    assert len(replies) == 0
