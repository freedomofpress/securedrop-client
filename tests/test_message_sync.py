"""
Make sure the message sync object behaves as expected.
"""
from securedrop_client.crypto import CryptoError
from securedrop_client.message_sync import MessageSync, ReplySync


def test_MessageSync_init(mocker):
    """
    Ensure things are set up as expected
    """
    # patch the session and use our own
    mock_session_class = mocker.MagicMock()
    mocker.patch('securedrop_client.db.make_engine')
    mocker.patch('securedrop_client.message_sync.sessionmaker', return_value=mock_session_class)

    # don't create a GpgHelper because it will error on missing directories
    mocker.patch('securedrop_client.message_sync.GpgHelper')

    api = mocker.MagicMock()
    home = "/home/user/.sd"
    is_qubes = False

    ms = MessageSync(api, home, is_qubes)

    assert ms.home == "/home/user/.sd"
    assert ms.api == api
    assert ms.session == mock_session_class()


def test_MessageSync_run_success(mocker):
    submission = mocker.MagicMock()
    submission.uuid = 'mock id'
    submission.download_url = "http://foo"
    submission.filename = "foo.gpg"

    # mock the fetching of submissions
    mocker.patch('securedrop_client.storage.find_new_submissions', return_value=[submission])
    mocker.patch('securedrop_client.message_sync.storage.mark_file_as_downloaded')
    # don't create the signal
    mocker.patch('securedrop_client.message_sync.pyqtSignal')
    # mock the GpgHelper creation since we don't have directories/keys setup
    mocker.patch('securedrop_client.message_sync.GpgHelper')

    api = mocker.MagicMock()
    home = "/home/user/.sd"
    is_qubes = True

    ms = MessageSync(api, home, is_qubes)
    ms.api.download_submission = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    mock_message_downloaded = mocker.Mock()
    mock_emit = mocker.Mock()
    mock_message_downloaded.emit = mock_emit
    mocker.patch.object(ms, 'message_downloaded', new=mock_message_downloaded)

    # check that it runs without raising exceptions
    ms.run(False)

    assert mock_emit.called


def test_MessageSync_exception(homedir, config, mocker):
    """
    Mostly here for code coverage- makes sure that if an exception is
    raised in the download thread, the code which catches it is actually
    run.
    Using the `config` fixture to ensure the config is written to disk.
    """
    submission = mocker.MagicMock()
    api = mocker.MagicMock()
    is_qubes = False

    # mock to return the submission we want
    mocker.patch('securedrop_client.storage.find_new_submissions', return_value=[submission])
    # mock to prevent GpgHelper from raising errors on init
    mocker.patch('securedrop_client.crypto.safe_mkdir')

    ms = MessageSync(api, str(homedir), is_qubes)
    mocker.patch.object(ms.gpg, 'decrypt_submission_or_reply', side_effect=CryptoError)

    # check that it runs without raising exceptions
    ms.run(False)


def test_MessageSync_run_failure(mocker):
    submission = mocker.MagicMock()
    submission.download_url = "http://foo"
    submission.filename = "foo.gpg"

    # mock the fetching of submissions
    mocker.patch('securedrop_client.storage.find_new_submissions', return_value=[submission])
    # mock the handling of the downloaded files
    mocker.patch('securedrop_client.message_sync.storage.mark_file_as_downloaded')
    # mock the GpgHelper creation since we don't have directories/keys setup
    mocker.patch('securedrop_client.message_sync.GpgHelper')

    api = mocker.MagicMock()
    home = "/home/user/.sd"
    is_qubes = False

    ms = MessageSync(api, home, is_qubes)
    ms.api.download_submission = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    # check that it runs without raising exceptions
    ms.run(False)


def test_ReplySync_run_success(mocker):
    reply = mocker.MagicMock()
    reply.uuid = 'mock id'
    reply.download_url = "http://foo"
    reply.filename = "foo.gpg"

    api = mocker.MagicMock()
    home = "/home/user/.sd"
    is_qubes = True

    # mock the fetching of replies
    mocker.patch('securedrop_client.storage.find_new_replies', return_value=[reply])
    # don't create the signal
    mocker.patch('securedrop_client.message_sync.pyqtSignal')
    # mock the handling of the replies
    mocker.patch('securedrop_client.message_sync.storage.mark_reply_as_downloaded')
    mocker.patch('securedrop_client.message_sync.GpgHelper')

    api = mocker.MagicMock()
    home = "/home/user/.sd"
    is_qubes = True

    ms = ReplySync(api, home, is_qubes)
    ms.api.download_reply = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    mock_reply_downloaded = mocker.Mock()
    mock_emit = mocker.Mock()
    mock_reply_downloaded.emit = mock_emit
    mocker.patch.object(ms, 'reply_downloaded', new=mock_reply_downloaded)

    # check that it runs without raising exceptions
    ms.run(False)

    assert mock_emit.called


def test_ReplySync_exception(mocker):
    """
    Mostly here for code coverage- makes sure that if an exception is
    raised in the download thread, the code which catches it is actually
    run
    """
    reply = mocker.MagicMock()
    api = mocker.MagicMock()
    home = "/home/user/.sd"
    is_qubes = False

    mocker.patch('securedrop_client.storage.find_new_replies', return_value=[reply])
    mocker.patch('securedrop_client.message_sync.GpgHelper')
    mocker.patch("sdclientapi.sdlocalobjects.Reply", mocker.MagicMock(side_effect=Exception()))

    rs = ReplySync(api, home, is_qubes)

    # check that it runs without raise exceptions
    rs.run(False)


def test_ReplySync_run_failure(mocker):
    reply = mocker.MagicMock()
    reply.download_url = "http://foo"
    reply.filename = "foo.gpg"

    # mock finding new replies
    mocker.patch('securedrop_client.storage.find_new_replies', return_value=[reply])
    # mock handling the new reply
    mocker.patch('securedrop_client.message_sync.storage.mark_file_as_downloaded')
    mocker.patch('securedrop_client.message_sync.GpgHelper')

    api = mocker.MagicMock()
    home = "/home/user/.sd"
    is_qubes = False

    ms = ReplySync(api, home, is_qubes)
    ms.api.download_submission = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    # check that it runs without raise exceptions
    ms.run(False)
