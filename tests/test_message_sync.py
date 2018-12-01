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
    mocker.patch('securedrop_client.models.make_engine')
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
    submission.download_url = "http://foo"
    submission.filename = "foo.gpg"

    fh = mocker.MagicMock()
    fh.name = "foo"

    # mock the fetching of submissions
    mocker.patch('securedrop_client.storage.find_new_submissions', return_value=[submission])
    # mock the handling of the downloaded files
    mocker.patch('shutil.move')
    mocker.patch('os.unlink')
    mocker.patch('tempfile.NamedTemporaryFile', return_value=fh)
    mocker.patch('securedrop_client.message_sync.storage.mark_file_as_downloaded')
    mocker.patch('builtins.open', mocker.mock_open(read_data="blah"))
    # mock the GpgHelper creation since we don't have directories/keys setup
    mocker.patch('securedrop_client.message_sync.GpgHelper')

    api = mocker.MagicMock()
    home = "/home/user/.sd"
    is_qubes = True

    ms = MessageSync(api, home, is_qubes)
    ms.api.download_submission = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    # check that it runs without raising exceptions
    ms.run(False)


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
    ms.run(False)


def test_MessageSync_run_failure(mocker):
    submission = mocker.MagicMock()
    submission.download_url = "http://foo"
    submission.filename = "foo.gpg"

    fh = mocker.MagicMock()
    fh.name = "foo"

    # mock the fetching of submissions
    mocker.patch('securedrop_client.storage.find_new_submissions', return_value=[submission])
    # mock the handling of the downloaded files
    mocker.patch('shutil.move')
    mocker.patch('os.unlink')
    mocker.patch('securedrop_client.message_sync.storage.mark_file_as_downloaded')
    mocker.patch('tempfile.NamedTemporaryFile', return_value=fh)
    mocker.patch('builtins.open', mocker.mock_open(read_data="blah"))
    # mock the GpgHelper creation since we don't have directories/keys setup
    mocker.patch('securedrop_client.message_sync.GpgHelper')

    api = mocker.MagicMock()
    home = "/home/user/.sd"
    is_qubes = False

    ms = MessageSync(api, home, is_qubes)
    ms.api.download_submission = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    ms.run(False)


def test_ReplySync_run_success(mocker):
    reply = mocker.MagicMock()
    reply.download_url = "http://foo"
    reply.filename = "foo.gpg"

    fh = mocker.MagicMock()
    fh.name = "foo"

    api = mocker.MagicMock()
    home = "/home/user/.sd"
    is_qubes = True

    # mock the fetching of replies
    mocker.patch('securedrop_client.storage.find_new_replies', return_value=[reply])
    # mock the handling of the replies
    mocker.patch('shutil.move')
    mocker.patch('os.unlink')
    mocker.patch('securedrop_client.message_sync.storage.mark_file_as_downloaded')
    mocker.patch('tempfile.NamedTemporaryFile', return_value=fh)
    mocker.patch('securedrop_client.message_sync.GpgHelper')
    mocker.patch('builtins.open', mocker.mock_open(read_data="blah"))

    api = mocker.MagicMock()
    home = "/home/user/.sd"
    is_qubes = True

    ms = ReplySync(api, home, is_qubes)
    ms.api.download_reply = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    # check that it runs without raising exceptions
    ms.run(False)


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
    rs.run(False)


def test_ReplySync_run_failure(mocker):
    reply = mocker.MagicMock()
    reply.download_url = "http://foo"
    reply.filename = "foo.gpg"

    fh = mocker.MagicMock()
    fh.name = "foo"

    # mock finding new replies
    mocker.patch('securedrop_client.storage.find_new_replies', return_value=[reply])
    # mock handling the new reply
    mocker.patch('shutil.move')
    mocker.patch('os.unlink')
    mocker.patch('securedrop_client.message_sync.storage.mark_file_as_downloaded')
    mocker.patch('tempfile.NamedTemporaryFile', return_value=fh)
    mocker.patch('securedrop_client.message_sync.GpgHelper')
    mocker.patch('builtins.open', mocker.mock_open(read_data="blah"))

    api = mocker.MagicMock()
    home = "/home/user/.sd"
    is_qubes = False

    ms = ReplySync(api, home, is_qubes)
    ms.api.download_submission = mocker.MagicMock(return_value=(1234, "/home/user/downloads/foo"))

    # check that it runs without raise exceptions
    ms.run(False)
