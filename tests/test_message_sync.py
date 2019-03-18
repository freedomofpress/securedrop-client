"""
Make sure the message sync object behaves as expected.
"""
from securedrop_client.crypto import CryptoError
from securedrop_client.message_sync import MessageSync, ReplySync
from tests import factory


def test_MessageSync_init(mocker, homedir):
    """
    Ensure things are set up as expected
    """
    # patch the session and use our own
    mock_session_class = mocker.MagicMock()
    mocker.patch('securedrop_client.db.make_engine')
    mocker.patch('securedrop_client.message_sync.sessionmaker', return_value=mock_session_class)

    api = mocker.MagicMock()
    is_qubes = False

    ms = MessageSync(api, homedir, is_qubes)

    assert ms.home == homedir
    assert ms.api == api
    assert ms.session == mock_session_class()


def test_MessageSync_run_success(mocker, session, source):
    """Test when a message successfully downloads and decrypts."""
    message = factory.Message(source=source['source'],
                              is_downloaded=False,
                              is_decrypted=None,
                              content=None)
    session.add(message)
    session.commit()

    expected_content = 'foo'

    def set_object_decryption_status_with_content_side_effect(*nargs, **kwargs):
        message.content = expected_content

    # mock the fetching of submissions
    mocker.patch('securedrop_client.storage.find_new_messages', return_value=[message])
    mock_download_status = mocker.patch(
        'securedrop_client.message_sync.storage.mark_message_as_downloaded')
    mock_decryption_status = mocker.patch(
        'securedrop_client.message_sync.storage.set_object_decryption_status_with_content',
        side_effect=set_object_decryption_status_with_content_side_effect)

    # don't create the signal
    mocker.patch('securedrop_client.message_sync.pyqtSignal')

    def mock_decrypt_submission_or_reply(filepath, plaintext_filename, is_doc):
        with open(plaintext_filename, 'w') as f:
            f.write(expected_content)

    # mock the GpgHelper creation since we don't have directories/keys setup
    mock_gpg_helper = mocker.MagicMock(decrypt_submission_or_reply=mock_decrypt_submission_or_reply)
    mocker.patch('securedrop_client.message_sync.GpgHelper', return_value=mock_gpg_helper)

    api = mocker.MagicMock(session=session)
    ms = MessageSync(api, 'mock', True)
    ms.session = session  # "patch" it with a real session
    ms.api.download_submission = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    mock_message_ready = mocker.patch.object(ms, 'message_ready')

    # check that it runs without raising exceptions
    ms.run(False)

    mock_decryption_status.assert_called_once_with(message, api.session, True, expected_content)
    mock_download_status.called_once_with(message, api.mock_session)
    mock_message_ready.emit.assert_called_once_with(message.uuid, expected_content)


def test_MessageSync_run_decryption_error(mocker, session, source):
    """Test when a message successfully downloads, but does not successfully decrypt."""
    message = factory.Message(source=source['source'],
                              is_downloaded=False,
                              is_decrypted=None,
                              content=None)
    session.add(message)
    session.commit()

    # mock the fetching of submissions
    mocker.patch('securedrop_client.storage.find_new_messages', return_value=[message])
    mock_download_status = mocker.patch(
        'securedrop_client.message_sync.storage.mark_message_as_downloaded')
    mock_decryption_status = mocker.patch(
        'securedrop_client.message_sync.storage.set_object_decryption_status_with_content')

    # don't create the signal
    mocker.patch('securedrop_client.message_sync.pyqtSignal')
    # mock the GpgHelper creation since we don't have directories/keys setup
    mocker.patch('securedrop_client.message_sync.GpgHelper')

    api = mocker.MagicMock(session=session)

    ms = MessageSync(api, 'mock', True)
    ms.session = session  # "patch" it with a real session
    mocker.patch.object(ms.gpg, 'decrypt_submission_or_reply', side_effect=CryptoError)

    ms.api.download_submission = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    mock_message_ready = mocker.patch.object(ms, 'message_ready')

    # check that it runs without raising exceptions
    ms.run(False)

    mock_download_status.assert_called_once_with(message.uuid, session)
    mock_decryption_status.assert_called_once_with(message, api.session, False)
    mock_message_ready.emit.assert_called_once_with(message.uuid, '<Message not yet available>')


def test_MessageSync_exception(homedir, config, mocker, source):
    """
    Mostly here for code coverage- makes sure that if an exception is
    raised in the download thread, the code which catches it is actually
    run.
    Using the `config` fixture to ensure the config is written to disk.
    """
    message = factory.Message(source=source['source'])
    api = mocker.MagicMock()
    is_qubes = False

    # mock to return the submission we want
    mocker.patch('securedrop_client.storage.find_new_messages', return_value=[message])
    mocker.patch('securedrop_client.storage.find_new_files', return_value=[])
    # mock to prevent GpgHelper from raising errors on init
    mocker.patch('securedrop_client.crypto.safe_mkdir')

    ms = MessageSync(api, str(homedir), is_qubes)
    mocker.patch.object(ms.gpg, 'decrypt_submission_or_reply', side_effect=CryptoError)

    # check that it runs without raising exceptions
    ms.run(False)


def test_MessageSync_run_failure(mocker, source):
    message = factory.Message(source=source['source'])

    # mock the fetching of submissions
    mocker.patch('securedrop_client.storage.find_new_messages', return_value=[message])
    mocker.patch('securedrop_client.storage.find_new_files', return_value=[])
    # mock the handling of the downloaded files
    mocker.patch('securedrop_client.message_sync.storage.mark_file_as_downloaded')
    mocker.patch('securedrop_client.message_sync.storage.mark_message_as_downloaded')
    # mock the GpgHelper creation since we don't have directories/keys setup
    mocker.patch('securedrop_client.message_sync.GpgHelper')

    api = mocker.MagicMock()
    home = "/home/user/.sd"
    is_qubes = False

    ms = MessageSync(api, home, is_qubes)
    ms.api.download_submission = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    # check that it runs without raising exceptions
    ms.run(False)


def test_ReplySync_run_success(mocker, session, source):
    """Test when a reply successfully downloads and decrypts."""
    reply = factory.Reply(source=source['source'],
                          is_downloaded=False,
                          is_decrypted=None,
                          content=None)
    session.add(reply)
    session.commit()

    expected_content = 'foo'

    def set_object_decryption_status_with_content_side_effect(*nargs, **kwargs):
        reply.content = expected_content

    # mock the fetching of replies
    mocker.patch('securedrop_client.storage.find_new_replies', return_value=[reply])
    mock_download_status = mocker.patch(
        'securedrop_client.message_sync.storage.mark_reply_as_downloaded')
    mock_decryption_status = mocker.patch(
        'securedrop_client.message_sync.storage.set_object_decryption_status_with_content',
        side_effect=set_object_decryption_status_with_content_side_effect)

    # don't create the signal
    mocker.patch('securedrop_client.message_sync.pyqtSignal')

    def mock_decrypt_submission_or_reply(filepath, plaintext_filename, is_doc):
        with open(plaintext_filename, 'w') as f:
            f.write(expected_content)

    # mock the GpgHelper creation since we don't have directories/keys setup
    mock_gpg_helper = mocker.MagicMock(decrypt_submission_or_reply=mock_decrypt_submission_or_reply)
    mocker.patch('securedrop_client.message_sync.GpgHelper', return_value=mock_gpg_helper)

    api = mocker.MagicMock(session=session)
    rs = ReplySync(api, 'mock', True)
    rs.session = session  # "patch" it with a real session
    rs.api.download_reply = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    mock_reply_ready = mocker.patch.object(rs, 'reply_ready')

    # check that it runs without raising exceptions
    rs.run(False)

    mock_decryption_status.assert_called_once_with(reply, api.session, True, expected_content)
    mock_download_status.called_once_with(reply, api.mock_session)
    mock_reply_ready.emit.assert_called_once_with(reply.uuid, expected_content)


def test_ReplySync_exception(mocker):
    """
    Mostly here for code coverage- makes sure that if an exception is
    raised in the download thread, the code which catches it is actually
    run
    """
    reply = factory.Reply()
    api = mocker.MagicMock()
    home = "/home/user/.sd"
    is_qubes = False

    mocker.patch('securedrop_client.storage.find_new_replies', return_value=[reply])
    mocker.patch('securedrop_client.message_sync.GpgHelper')
    mocker.patch("sdclientapi.sdlocalobjects.Reply", mocker.MagicMock(side_effect=Exception()))

    rs = ReplySync(api, home, is_qubes)

    # check that it runs without raise exceptions
    rs.run(False)


def test_ReplySync_run_decryption_error(mocker, session, source):
    """Test when a reply successfully downloads, but does not successfully decrypt."""
    reply = factory.Reply(source=source['source'],
                          is_downloaded=False,
                          is_decrypted=None,
                          content=None)
    session.add(reply)
    session.commit()

    # mock the fetching of replies
    mocker.patch('securedrop_client.storage.find_new_replies', return_value=[reply])
    mock_download_status = mocker.patch(
        'securedrop_client.message_sync.storage.mark_reply_as_downloaded')
    mock_decryption_status = mocker.patch(
        'securedrop_client.message_sync.storage.set_object_decryption_status_with_content')

    # don't create the signal
    mocker.patch('securedrop_client.message_sync.pyqtSignal')
    # mock the GpgHelper creation since we don't have directories/keys setup
    mocker.patch('securedrop_client.message_sync.GpgHelper')

    api = mocker.MagicMock(session=session)

    rs = ReplySync(api, 'mock', True)
    rs.session = session  # "patch" it with a real session
    mocker.patch.object(rs.gpg, 'decrypt_submission_or_reply', side_effect=CryptoError)

    rs.api.download_reply = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    mock_reply_ready = mocker.patch.object(rs, 'reply_ready')

    # check that it runs without raising exceptions
    rs.run(False)

    mock_download_status.assert_called_once_with(reply.uuid, session)
    mock_decryption_status.assert_called_once_with(reply, api.session, False)
    mock_reply_ready.emit.assert_called_once_with(reply.uuid, '<Reply not yet available>')


def test_ReplySync_run_failure(mocker, session, source):
    reply = factory.Reply(source=source['source'])
    session.add(reply)
    session.commit()

    # mock finding new replies
    mocker.patch('securedrop_client.storage.find_new_replies', return_value=[reply])
    # mock handling the new reply
    mocker.patch('securedrop_client.message_sync.storage.mark_reply_as_downloaded')
    mocker.patch('securedrop_client.message_sync.GpgHelper')

    api = mocker.MagicMock()
    home = "/home/user/.sd"
    is_qubes = False

    ms = ReplySync(api, home, is_qubes)
    ms.api.download_submission = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    # check that it runs without raise exceptions
    ms.run(False)
