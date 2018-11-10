"""
Make sure the message sync object behaves as expected.
"""
from unittest import mock
from securedrop_client.message_sync import MessageSync, ReplySync


def test_MessageSync_init():
    """
    Ensure things are set up as expected
    """
    mock_session_class = mock.MagicMock()
    with mock.patch('securedrop_client.models.make_engine'), \
        mock.patch('securedrop_client.message_sync.sessionmaker',
                   return_value=mock_session_class):

        api = mock.MagicMock()
        home = "/home/user/.sd"
        is_qubes = False

        ms = MessageSync(api, home, is_qubes)

        assert ms.home == "/home/user/.sd"
        assert ms.api == api
        assert ms.session == mock_session_class()


def test_MessageSync_run_success():
    submission = mock.MagicMock()
    submission.download_url = "http://foo"
    submission.filename = "foo.gpg"

    fh = mock.MagicMock()
    fh.name = "foo"

    with mock.patch('securedrop_client.storage.find_new_submissions',
                    return_value=[
                        submission
                    ]),\
            mock.patch('subprocess.call',
                       return_value=0), \
            mock.patch('shutil.move'), \
            mock.patch('shutil.copy'), \
            mock.patch('os.unlink'), \
            mock.patch('securedrop_client.message_sync.storage'
                       '.mark_file_as_downloaded'), \
            mock.patch(
                'tempfile.NamedTemporaryFile',
                return_value=fh), \
            mock.patch('builtins.open', mock.mock_open(read_data="blah")):

        api = mock.MagicMock()
        home = "/home/user/.sd"
        is_qubes = True

        ms = MessageSync(api, home, is_qubes)
        ms.api.download_submission = mock.MagicMock(
            return_value=(1234, "/home/user/downloads/foo")
        )

        ms.run(False)


def test_MessageSync_exception():
    """
    Mostly here for code coverage- makes sure that if an exception is
    raised in the download thread, the code which catches it is actually
    run
    """
    submission = mock.MagicMock()
    api = mock.MagicMock()
    home = "/home/user/.sd"
    is_qubes = False
    ms = MessageSync(api, home, is_qubes)

    with mock.patch('securedrop_client.storage.find_new_submissions',
                    return_value=[
                        submission
                    ]),\
        mock.patch("sdclientapi.sdlocalobjects.Submission",
                   mock.MagicMock(side_effect=Exception())):
        ms.run(False)


def test_MessageSync_run_failure():
    submission = mock.MagicMock()
    submission.download_url = "http://foo"
    submission.filename = "foo.gpg"

    fh = mock.MagicMock()
    fh.name = "foo"

    with mock.patch('securedrop_client.storage.find_new_submissions',
                    return_value=[
                        submission
                    ]),\
            mock.patch('subprocess.call',
                       return_value=1), \
            mock.patch('shutil.move'), \
            mock.patch('shutil.copy'), \
            mock.patch('os.unlink'), \
            mock.patch('securedrop_client.message_sync.storage'
                       '.mark_file_as_downloaded'), \
            mock.patch(
                'tempfile.NamedTemporaryFile',
                return_value=fh), \
            mock.patch('builtins.open', mock.mock_open(read_data="blah")):

        api = mock.MagicMock()
        home = "/home/user/.sd"
        is_qubes = False

        ms = MessageSync(api, home, is_qubes)
        ms.api.download_submission = mock.MagicMock(
            return_value=(1234, "/home/user/downloads/foo")
        )

        ms.run(False)


def test_ReplySync_run_success():
    reply = mock.MagicMock()
    reply.download_url = "http://foo"
    reply.filename = "foo.gpg"

    fh = mock.MagicMock()
    fh.name = "foo"

    with mock.patch('securedrop_client.storage.find_new_replies',
                    return_value=[
                        reply
                    ]),\
            mock.patch('subprocess.call',
                       return_value=0), \
            mock.patch('shutil.move'), \
            mock.patch('shutil.copy'), \
            mock.patch('os.unlink'), \
            mock.patch('securedrop_client.message_sync.storage'
                       '.mark_file_as_downloaded'), \
            mock.patch(
                'tempfile.NamedTemporaryFile',
                return_value=fh), \
            mock.patch('builtins.open', mock.mock_open(read_data="blah")):

        api = mock.MagicMock()
        home = "/home/user/.sd"
        is_qubes = True

        ms = ReplySync(api, home, is_qubes)
        ms.api.download_reply = mock.MagicMock(
            return_value=(1234, "/home/user/downloads/foo")
        )

        ms.run(False)


def test_ReplySync_exception():
    """
    Mostly here for code coverage- makes sure that if an exception is
    raised in the download thread, the code which catches it is actually
    run
    """
    reply = mock.MagicMock()
    api = mock.MagicMock()
    home = "/home/user/.sd"
    is_qubes = False
    rs = ReplySync(api, home, is_qubes)

    with mock.patch('securedrop_client.storage.find_new_replies',
                    return_value=[
                        reply
                    ]),\
        mock.patch("sdclientapi.sdlocalobjects.Reply",
                   mock.MagicMock(side_effect=Exception())):
        rs.run(False)


def test_ReplySync_run_failure():
    reply = mock.MagicMock()
    reply.download_url = "http://foo"
    reply.filename = "foo.gpg"

    fh = mock.MagicMock()
    fh.name = "foo"

    with mock.patch('securedrop_client.storage.find_new_replies',
                    return_value=[
                        reply
                    ]),\
            mock.patch('subprocess.call',
                       return_value=1), \
            mock.patch('shutil.move'), \
            mock.patch('shutil.copy'), \
            mock.patch('os.unlink'), \
            mock.patch('securedrop_client.message_sync.storage'
                       '.mark_reply_as_downloaded'), \
            mock.patch(
                'tempfile.NamedTemporaryFile',
                return_value=fh), \
            mock.patch('builtins.open', mock.mock_open(read_data="blah")):

        api = mock.MagicMock()
        home = "/home/user/.sd"
        is_qubes = False

        ms = ReplySync(api, home, is_qubes)
        ms.api.download_submission = mock.MagicMock(
            return_value=(1234, "/home/user/downloads/foo")
        )

        ms.run(False)
