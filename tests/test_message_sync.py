"""
Make sure the message sync object behaves as expected.
"""
import pytest
from unittest import mock
from securedrop_client.message_sync import MessageSync

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

        ms = MessageSync(api, home)

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
            mock.patch('shutil.move') as mock_move, \
            mock.patch('shutil.copy') as mock_copy, \
            mock.patch('os.unlink') as mock_unlink, \
            mock.patch(
              'securedrop_client.message_sync.storage.mark_file_as_downloaded' \
            ) as mock_mark_as_dl, \
            mock.patch(
                'tempfile.NamedTemporaryFile',
                return_value=fh) as mock_temp_file, \
            mock.patch('builtins.open', mock.mock_open(read_data="blah")):

        api = mock.MagicMock()
        home = "/home/user/.sd"

        ms = MessageSync(api, home)
        ms.api.download_submission_from_url = mock.MagicMock(
            return_value=(1234, "/tmp/foo")
        )

        ms.run(False)

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
            mock.patch('shutil.move') as mock_move, \
            mock.patch('shutil.copy') as mock_copy, \
            mock.patch('os.unlink') as mock_unlink, \
            mock.patch(
              'securedrop_client.message_sync.storage.mark_file_as_downloaded' \
            ) as mock_mark_as_dl, \
            mock.patch(
                'tempfile.NamedTemporaryFile',
                return_value=fh) as mock_temp_file, \
            mock.patch('builtins.open', mock.mock_open(read_data="blah")):


        api = mock.MagicMock()
        home = "/home/user/.sd"

        ms = MessageSync(api, home)
        ms.api.download_submission_from_url = mock.MagicMock(
            return_value=(1234, "/tmp/foo")
        )

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
            mock.patch('shutil.move') as mock_move, \
            mock.patch('shutil.copy') as mock_copy, \
            mock.patch('os.unlink') as mock_unlink, \
            mock.patch(
              'securedrop_client.message_sync.storage.mark_file_as_downloaded' \
            ) as mock_mark_as_dl, \
            mock.patch(
                'tempfile.NamedTemporaryFile',
                return_value=fh) as mock_temp_file, \
            mock.patch('builtins.open', mock.mock_open(read_data="blah")):


        api = mock.MagicMock()
        home = "/home/user/.sd"

        ms = MessageSync(api, home)
        ms.api.download_submission_from_url = mock.MagicMock(
            return_value=(1234, "/tmp/foo")
        )

        ms.run(False)
