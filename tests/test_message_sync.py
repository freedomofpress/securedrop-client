"""
Make sure the message sync object behaves as expected.
"""
from securedrop_client.crypto import GpgHelper, CryptoError
from securedrop_client.message_sync import MessageSync, ReplySync
from tests import factory


def test_MessageSync_init(mocker, session_maker):
    """
    Ensure things are set up as expected
    """

    mock_api = mocker.MagicMock()
    mock_gpg = mocker.MagicMock()

    ms = MessageSync(mock_api, mock_gpg, session_maker)

    assert ms.api == mock_api
    assert ms.gpg == mock_gpg
    assert ms.session_maker == session_maker


def test_MessageSync_run_success(mocker, session, source, session_maker, homedir):
    """
    Test when a message successfully downloads and decrypts.
    Using the `homedir` fixture to get a GPG keyring.
    """
    message = factory.Message(source=source['source'],
                              is_downloaded=False,
                              is_decrypted=None,
                              content=None)
    session.add(message)
    session.commit()

    expected_content = 'foo'

    # don't create the signal
    mocker.patch('securedrop_client.message_sync.pyqtSignal')

    def mock_decrypt_submission_or_reply(filepath, plaintext_filename, is_doc):
        with open(plaintext_filename, 'w') as f:
            f.write(expected_content)

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    mocker.patch.object(
        gpg,
        'decrypt_submission_or_reply',
        side_effect=mock_decrypt_submission_or_reply,
    )

    api = mocker.MagicMock(session=session)
    ms = MessageSync(api, gpg, session_maker)
    ms.api.download_submission = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    mock_message_ready = mocker.patch.object(ms, 'message_ready')

    # check that it runs without raising exceptions
    ms.run(False)

    mock_message_ready.emit.assert_called_once_with(message.uuid, expected_content)

    session.refresh(message)
    assert message.content == expected_content
    assert message.is_downloaded is True
    assert message.is_decrypted is True


def test_MessageSync_run_decrypt_only(mocker, session, source, session_maker, homedir):
    """
    Test when a message successfully downloads and decrypts.
    Using the `homedir` fixture to get a GPG keyring.
    """
    message = factory.Message(source=source['source'],
                              is_downloaded=True,
                              is_decrypted=False,
                              content=None)
    session.add(message)
    session.commit()

    expected_content = 'foo'

    # don't create the signal
    mocker.patch('securedrop_client.message_sync.pyqtSignal')

    def mock_decrypt_submission_or_reply(filepath, plaintext_filename, is_doc):
        with open(plaintext_filename, 'w') as f:
            f.write(expected_content)

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    mocker.patch.object(
        gpg,
        'decrypt_submission_or_reply',
        side_effect=mock_decrypt_submission_or_reply,
    )

    api = mocker.MagicMock(session=session)
    ms = MessageSync(api, gpg, session_maker)
    ms.api.download_submission = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))
    mock_fetch = mocker.patch.object(ms, 'fetch_the_thing')

    mock_message_ready = mocker.patch.object(ms, 'message_ready')

    # check that it runs without raising exceptions
    ms.run(False)

    mock_message_ready.emit.assert_called_once_with(message.uuid, expected_content)

    session.refresh(message)
    assert message.content == expected_content
    assert message.is_downloaded is True
    assert message.is_decrypted is True
    assert not mock_fetch.called


def test_MessageSync_run_decryption_error(mocker, session, source, session_maker, homedir):
    """
    Test when a message successfully downloads, but does not successfully decrypt.
    Using the `homedir` fixture to get a GPG keyring.
    """
    message = factory.Message(source=source['source'],
                              is_downloaded=False,
                              is_decrypted=None,
                              content=None)
    session.add(message)
    session.commit()

    # don't create the signal
    mocker.patch('securedrop_client.message_sync.pyqtSignal')

    api = mocker.MagicMock(session=session)

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)

    ms = MessageSync(api, gpg, session_maker)
    mocker.patch.object(ms.gpg, 'decrypt_submission_or_reply', side_effect=CryptoError)

    ms.api.download_submission = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    mock_message_ready = mocker.patch.object(ms, 'message_ready')

    # check that it runs without raising exceptions
    ms.run(False)

    mock_message_ready.emit.assert_called_once_with(message.uuid, '<Message not yet available>')
    assert message.content is None
    assert message.is_downloaded is True
    assert message.is_decrypted is False


def test_MessageSync_exception(homedir, config, mocker, source, session, session_maker):
    """
    Makes sure that if an exception is raised in the download thread, the code which catches it is
    actually run.
    Using the `config` fixture to ensure the config is written to disk.
    """
    message = factory.Message(source=source['source'],
                              is_downloaded=False,
                              is_decrypted=None,
                              content=None)
    session.add(message)
    session.commit()

    mock_message = mocker.patch("sdclientapi.sdlocalobjects.Submission",
                                mocker.MagicMock(side_effect=Exception()))

    api = mocker.MagicMock()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    ms = MessageSync(api, gpg, session_maker)

    # check that it runs without raising exceptions
    ms.run(False)

    # ensure this was called and an exception was raised somewhere
    assert mock_message.called


def test_MessageSync_run_failure(mocker, source, session, session_maker, homedir):
    message = factory.Message(source=source['source'])
    session.add(message)
    session.commit()

    api = mocker.MagicMock()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    ms = MessageSync(api, gpg, session_maker)
    ms.api.download_submission = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    # check that it runs without raising exceptions
    ms.run(False)


def test_ReplySync_init(mocker, session_maker):
    """
    Ensure things are set up as expected
    """

    mock_api = mocker.MagicMock()
    mock_gpg = mocker.MagicMock()

    rs = ReplySync(mock_api, mock_gpg, session_maker)

    assert rs.api == mock_api
    assert rs.gpg == mock_gpg
    assert rs.session_maker == session_maker


def test_ReplySync_run_success(mocker, session, source, session_maker, homedir):
    """
    Test when a reply successfully downloads and decrypts.
    Using the `homedir` fixture to get a GPG keyring.
    """
    reply = factory.Reply(source=source['source'],
                          is_downloaded=False,
                          is_decrypted=None,
                          content=None)
    session.add(reply)
    session.commit()

    expected_content = 'foo'

    # don't create the signal
    mocker.patch('securedrop_client.message_sync.pyqtSignal')

    def mock_decrypt_submission_or_reply(filepath, plaintext_filename, is_doc):
        with open(plaintext_filename, 'w') as f:
            f.write(expected_content)

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    mocker.patch.object(
        gpg,
        'decrypt_submission_or_reply',
        side_effect=mock_decrypt_submission_or_reply,
    )

    api = mocker.MagicMock(session=session)
    rs = ReplySync(api, gpg, session_maker)
    rs.api.download_reply = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    mock_reply_ready = mocker.patch.object(rs, 'reply_ready')

    # check that it runs without raising exceptions
    rs.run(False)

    mock_reply_ready.emit.assert_called_once_with(reply.uuid, expected_content)

    session.refresh(reply)
    assert reply.content == expected_content
    assert reply.is_downloaded is True
    assert reply.is_decrypted is True


def test_ReplySync_run_decrypt_only(mocker, session, source, session_maker, homedir):
    """
    Test when a message successfully downloads and decrypts.
    Using the `homedir` fixture to get a GPG keyring.
    """
    reply = factory.Reply(source=source['source'],
                          is_downloaded=True,
                          is_decrypted=False,
                          content=None)
    session.add(reply)
    session.commit()

    expected_content = 'foo'

    # don't create the signal
    mocker.patch('securedrop_client.message_sync.pyqtSignal')

    def mock_decrypt_submission_or_reply(filepath, plaintext_filename, is_doc):
        with open(plaintext_filename, 'w') as f:
            f.write(expected_content)

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    mocker.patch.object(
        gpg,
        'decrypt_submission_or_reply',
        side_effect=mock_decrypt_submission_or_reply,
    )

    api = mocker.MagicMock(session=session)
    rs = ReplySync(api, gpg, session_maker)
    rs.api.download_submission = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))
    mock_fetch = mocker.patch.object(rs, 'fetch_the_thing')

    mock_message_ready = mocker.patch.object(rs, 'reply_ready')

    # check that it runs without raising exceptions
    rs.run(False)

    mock_message_ready.emit.assert_called_once_with(reply.uuid, expected_content)

    session.refresh(reply)
    assert reply.content == expected_content
    assert reply.is_downloaded is True
    assert reply.is_decrypted is True
    assert not mock_fetch.called


def test_ReplySync_run_decryption_error(mocker, session, source, session_maker, homedir):
    """
    Test when a reply successfully downloads, but does not successfully decrypt.
    Using the `homedir` fixture to get a GPG keyring.
    """
    reply = factory.Reply(source=source['source'],
                          is_downloaded=False,
                          is_decrypted=None,
                          content=None)
    session.add(reply)
    session.commit()

    # don't create the signal
    mocker.patch('securedrop_client.message_sync.pyqtSignal')

    api = mocker.MagicMock(session=session)

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)

    rs = ReplySync(api, gpg, session_maker)
    mocker.patch.object(rs.gpg, 'decrypt_submission_or_reply', side_effect=CryptoError)

    rs.api.download_reply = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    mock_reply_ready = mocker.patch.object(rs, 'reply_ready')

    # check that it runs without raising exceptions
    rs.run(False)

    mock_reply_ready.emit.assert_called_once_with(reply.uuid, '<Reply not yet available>')
    assert reply.content is None
    assert reply.is_downloaded is True
    assert reply.is_decrypted is False


def test_ReplySync_exception(homedir, config, mocker, source, session, session_maker):
    """
    Makes sure that if an exception is raised in the download thread, the code which catches it is
    actually run.
    Using the `config` fixture to ensure the config is written to disk.
    """
    reply = factory.Reply(source=source['source'],
                          is_downloaded=False,
                          is_decrypted=None,
                          content=None)
    session.add(reply)
    session.commit()

    mock_reply = mocker.patch("sdclientapi.sdlocalobjects.Reply",
                              mocker.MagicMock(side_effect=Exception()))

    api = mocker.MagicMock()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    rs = ReplySync(api, gpg, session_maker)

    # check that it runs without raising exceptions
    rs.run(False)

    # ensure this was called and an exception was raised somewhere
    assert mock_reply.called


def test_ReplySync_run_failure(mocker, source, session, session_maker, homedir):
    reply = factory.Reply(source=source['source'])
    session.add(reply)
    session.commit()

    api = mocker.MagicMock()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    rs = ReplySync(api, gpg, session_maker)
    rs.api.download_reply = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    # check that it runs without raising exceptions
    rs.run(False)
