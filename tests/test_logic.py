"""
Make sure the Client object, containing the application logic, behaves as
expected.
"""
import arrow
import os
import pytest

from sdclientapi import sdlocalobjects
from tests import factory
from securedrop_client import storage, db
from securedrop_client.crypto import CryptoError
from securedrop_client.logic import APICallRunner, Client

with open(os.path.join(os.path.dirname(__file__), 'files', 'test-key.gpg.pub.asc')) as f:
    PUB_KEY = f.read()


def test_APICallRunner_init(mocker):
    """
    Ensure everything is set up as expected.
    """
    mock_api_call = mocker.MagicMock()
    mock_current_object = mocker.MagicMock()
    cr = APICallRunner(mock_api_call, mock_current_object, 'foo', bar='baz')
    assert cr.api_call == mock_api_call
    assert cr.current_object == mock_current_object
    assert cr.args == ('foo', )
    assert cr.kwargs == {'bar': 'baz', }


def test_APICallRunner_call_api(mocker):
    """
    A result is obtained so emit True and put the result in self.result.
    """
    mock_api_call = mocker.MagicMock(return_value='foo')
    mock_api_call.__name__ = 'my_function'
    mock_current_object = mocker.MagicMock()
    cr = APICallRunner(mock_api_call, mock_current_object, 'foo', bar='baz')
    cr.call_finished = mocker.MagicMock()
    cr.call_api()
    assert cr.result == 'foo'
    cr.call_finished.emit.assert_called_once_with()


def test_APICallRunner_with_exception(mocker):
    """
    An exception has occured so emit False.
    """
    ex = Exception('boom')
    mock_api_call = mocker.MagicMock(side_effect=ex)
    mock_api_call.__name__ = 'my_function'
    mock_current_object = mocker.MagicMock()
    cr = APICallRunner(mock_api_call, mock_current_object, 'foo', bar='baz')
    cr.call_finished = mocker.MagicMock()
    mocker.patch('securedrop_client.logic.QTimer')
    cr.call_api()
    assert cr.result == ex
    cr.call_finished.emit.assert_called_once_with()


def test_Client_init(homedir, config, mocker):
    """
    The passed in gui, app and session instances are correctly referenced and,
    where appropriate, have a reference back to the client.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost/', mock_gui, mock_session, homedir)
    assert cl.hostname == 'http://localhost/'
    assert cl.gui == mock_gui
    assert cl.session == mock_session
    assert cl.api_threads == {}


def test_Client_setup(homedir, config, mocker):
    """
    Ensure the application is set up with the following default state:
    Using the `config` fixture to ensure the config is written to disk.
    """
    cl = Client('http://localhost', mocker.MagicMock(), mocker.MagicMock(), homedir)
    cl.update_sources = mocker.MagicMock()

    cl.setup()

    cl.gui.setup.assert_called_once_with(cl)


def test_Client_start_message_thread(homedir, config, mocker):
    """
    When starting message-fetching thread, make sure we do a few things.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    mock_qthread = mocker.patch('securedrop_client.logic.QThread')
    mocker.patch('securedrop_client.logic.MessageSync')
    cl.message_sync = mocker.MagicMock()
    cl.start_message_thread()
    cl.message_sync.moveToThread.assert_called_once_with(mock_qthread())
    cl.message_thread.started.connect.assert_called_once_with(cl.message_sync.run)
    cl.message_thread.start.assert_called_once_with()


def test_Client_start_message_thread_if_already_running(homedir, config, mocker):
    """
    Ensure that when starting the message thread, we don't start another thread
    if it's already running. Instead, we just authenticate the existing thread.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.api = 'api object'
    cl.message_sync = mocker.MagicMock()
    cl.message_thread = mocker.MagicMock()
    cl.message_thread.api = None
    cl.start_message_thread()
    cl.message_sync.api = cl.api
    cl.message_thread.start.assert_not_called()


def test_Client_start_reply_thread(homedir, config, mocker):
    """
    When starting reply-fetching thread, make sure we do a few things.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    mock_qthread = mocker.patch('securedrop_client.logic.QThread')
    mocker.patch('securedrop_client.logic.ReplySync')
    cl.reply_sync = mocker.MagicMock()
    cl.start_reply_thread()
    cl.reply_sync.moveToThread.assert_called_once_with(mock_qthread())
    cl.reply_thread.started.connect.assert_called_once_with(
        cl.reply_sync.run)
    cl.reply_thread.start.assert_called_once_with()


def test_Client_start_reply_thread_if_already_running(homedir, config, mocker):
    """
    Ensure that when starting the reply thread, we don't start another thread
    if it's already running. Instead, we just authenticate the existing thread.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.api = 'api object'
    cl.reply_sync = mocker.MagicMock()
    cl.reply_thread = mocker.MagicMock()
    cl.reply_thread.api = None
    cl.start_reply_thread()
    cl.reply_sync.api = cl.api
    cl.reply_thread.start.assert_not_called()


def test_Client_call_api(homedir, config, mocker):
    """
    A new thread and APICallRunner is created / setup.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.finish_api_call = mocker.MagicMock()
    mocker.patch('securedrop_client.logic.QThread')
    mocker.patch('securedrop_client.logic.APICallRunner')
    mocker.patch('securedrop_client.logic.QTimer')
    mock_api_call = mocker.MagicMock()
    mock_callback = mocker.MagicMock()
    mock_timeout = mocker.MagicMock()

    cl.call_api(mock_api_call, mock_callback, mock_timeout, 'foo', bar='baz')

    assert len(cl.api_threads) == 1
    thread_info = cl.api_threads[list(cl.api_threads.keys())[0]]
    thread = thread_info['thread']
    runner = thread_info['runner']
    timer = thread_info['timer']
    thread.started.connect.assert_called_once_with(runner.call_api)
    thread.start.assert_called_once_with()
    runner.moveToThread.assert_called_once_with(thread)
    timer.timeout.connect.call_count == 1
    runner.call_finished.connect.call_count == 1


def test_Client_clean_thread_no_thread(homedir, config, mocker):
    """
    The client will ignore an attempt to reset an API call if there's no such
    call "in flight".
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.finish_api_call = mocker.MagicMock()
    cl.api_threads = {'a': 'b'}
    cl.clean_thread('foo')
    assert len(cl.api_threads) == 1


def test_Client_clean_thread(homedir, config, mocker):
    """
    Cleaning up an existing thread disconnects the timer and removes it from
    the api_threads collection.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    mock_timer = mocker.MagicMock()
    cl.api_threads = {
        'foo': {
            'timer': mock_timer,
        }
    }
    cl.clean_thread('foo')
    assert mock_timer.disconnect.call_count == 1
    assert 'foo' not in cl.api_threads


def test_Client_login(homedir, config, mocker):
    """
    Ensures the API is called in the expected manner for logging in the user
    given the username, password and 2fa token.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.call_api = mocker.MagicMock()
    mock_api = mocker.patch('securedrop_client.logic.sdclientapi.API')
    cl.login('username', 'password', '123456')
    cl.call_api.assert_called_once_with(mock_api().authenticate,
                                        cl.on_authenticate,
                                        cl.on_login_timeout)


def test_Client_login_offline_mode(homedir, config, mocker):
    """
    Ensures user is not authenticated when logging in in offline mode and that the correct windows
    are displayed.
    """
    cl = Client('http://localhost', mocker.MagicMock(), mocker.MagicMock(), homedir)
    cl.call_api = mocker.MagicMock()
    cl.gui = mocker.MagicMock()
    cl.gui.show_main_window = mocker.MagicMock()
    cl.gui.hide_login = mocker.MagicMock()
    cl.sync_api = mocker.MagicMock()
    cl.start_message_thread = mocker.MagicMock()
    cl.start_reply_thread = mocker.MagicMock()
    cl.update_sources = mocker.MagicMock()

    cl.login_offline_mode()

    assert cl.call_api.called is False
    assert cl.is_authenticated is False
    cl.gui.show_main_window.assert_called_once_with()
    cl.gui.hide_login.assert_called_once_with()
    cl.sync_api.assert_called_once_with()
    cl.start_message_thread.assert_called_once_with()
    cl.update_sources.assert_called_once_with()


def test_Client_on_authenticate_failed(homedir, config, mocker):
    """
    If the server responds with a negative to the request to authenticate, make
    sure the user knows.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    result_data = 'false'
    cl.on_authenticate(result_data)
    mock_gui.show_login_error.\
        assert_called_once_with(error='There was a problem signing in. Please '
                                'verify your credentials and try again.')


def test_Client_on_authenticate_ok(homedir, config, mocker):
    """
    Ensure the client syncs when the user successfully logs in.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.sync_api = mocker.MagicMock()
    cl.api = mocker.MagicMock()
    cl.start_message_thread = mocker.MagicMock()
    cl.start_reply_thread = mocker.MagicMock()
    cl.api.username = 'test'

    cl.on_authenticate(True)

    cl.sync_api.assert_called_once_with()
    cl.start_message_thread.assert_called_once_with()
    cl.gui.show_main_window.assert_called_once_with('test')
    cl.gui.clear_error_status.assert_called_once_with()


def test_Client_completed_api_call_without_current_object(homedir, config, mocker):
    """
    Ensure that cleanup is performed if an API call returns in the expected
    time.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    mock_thread = mocker.MagicMock()
    mock_runner = mocker.MagicMock()
    mock_runner.result = 'result'
    mock_runner.current_object = None
    mock_timer = mocker.MagicMock()
    cl.api_threads = {
        'thread_uuid': {
            'thread': mock_thread,
            'runner': mock_runner,
            'timer': mock_timer,
        }
    }
    cl.clean_thread = mocker.MagicMock()
    mock_user_callback = mocker.MagicMock()
    cl.completed_api_call('thread_uuid', mock_user_callback)
    cl.clean_thread.assert_called_once_with('thread_uuid')
    mock_user_callback.assert_called_once_with('result')
    mock_timer.stop.assert_called_once_with()


def test_Client_completed_api_call_with_current_object(homedir, config, mocker):
    """
    Ensure that cleanup is performed if an API call returns in the expected
    time.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    mock_thread = mocker.MagicMock()
    mock_runner = mocker.MagicMock()
    mock_runner.result = 'result'
    mock_runner.current_object = 'current_object'
    mock_timer = mocker.MagicMock()
    cl.api_threads = {
        'thread_uuid': {
            'thread': mock_thread,
            'runner': mock_runner,
            'timer': mock_timer,
        }
    }
    cl.clean_thread = mocker.MagicMock()
    mock_user_callback = mocker.MagicMock()
    cl.completed_api_call('thread_uuid', mock_user_callback)
    cl.clean_thread.assert_called_once_with('thread_uuid')
    mock_user_callback.assert_called_once_with('result',
                                               current_object='current_object')
    mock_timer.stop.assert_called_once_with()


def test_Client_timeout_cleanup_without_current_object(homedir, config, mocker):
    """
    Ensure that cleanup is performed if an API call times out.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    mock_thread = mocker.MagicMock()
    mock_runner = mocker.MagicMock()
    mock_runner.current_object = None
    mock_timer = mocker.MagicMock()
    cl.api_threads = {
        'thread_uuid': {
            'thread': mock_thread,
            'runner': mock_runner,
            'timer': mock_timer,
        }
    }
    cl.clean_thread = mocker.MagicMock()
    mock_user_callback = mocker.MagicMock()
    cl.timeout_cleanup('thread_uuid', mock_user_callback)
    assert mock_runner.i_timed_out is True
    cl.clean_thread.assert_called_once_with('thread_uuid')
    mock_user_callback.assert_called_once_with()


def test_Client_timeout_cleanup_with_current_object(homedir, config, mocker):
    """
    Ensure that cleanup is performed if an API call times out.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    mock_thread = mocker.MagicMock()
    mock_runner = mocker.MagicMock()
    mock_runner.current_object = 'current_object'
    mock_timer = mocker.MagicMock()
    cl.api_threads = {
        'thread_uuid': {
            'thread': mock_thread,
            'runner': mock_runner,
            'timer': mock_timer,
        }
    }
    cl.clean_thread = mocker.MagicMock()
    mock_user_callback = mocker.MagicMock()
    cl.timeout_cleanup('thread_uuid', mock_user_callback)
    assert mock_runner.i_timed_out is True
    cl.clean_thread.assert_called_once_with('thread_uuid')
    mock_user_callback.assert_called_once_with(current_object='current_object')


def test_Client_on_sync_timeout(homedir, config, mocker):
    """
    Display error message in status bar if sync times out.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.api = "this is populated"
    cl.on_sync_timeout()
    assert cl.api is not None
    mock_gui.update_error_status.\
        assert_called_once_with(error='The connection to the SecureDrop '
                                'server timed out. Please try again.')


def test_Client_on_login_timeout(homedir, config, mocker):
    """
    Reset the form if the API call times out.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.call_reset = mocker.MagicMock()
    cl.on_login_timeout()
    assert cl.api is None
    mock_gui.show_login_error.\
        assert_called_once_with(error='The connection to the SecureDrop '
                                'server timed out. Please try again.')


def test_Client_on_action_requiring_login(homedir, config, mocker):
    """
    Ensure that when on_action_requiring_login is called, an error
    is shown in the GUI status area.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.on_action_requiring_login()
    mock_gui.update_error_status.assert_called_once_with(
        'You must sign in to perform this action.')


def test_Client_authenticated_yes(homedir, config, mocker):
    """
    If the API is authenticated return True.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.api = mocker.MagicMock()
    cl.api.token = {'token': 'foo'}
    assert cl.authenticated() is True


def test_Client_authenticated_no(homedir, config, mocker):
    """
    If the API is authenticated return True.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.api = mocker.MagicMock()
    cl.api.token = {'token': ''}
    assert cl.authenticated() is False


def test_Client_authenticated_no_api(homedir, config, mocker):
    """
    If the API is authenticated return True.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.api = None
    assert cl.authenticated() is False


def test_Client_sync_api_not_authenticated(homedir, config, mocker):
    """
    If the API isn't authenticated, don't sync.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.authenticated = mocker.MagicMock(return_value=False)
    cl.call_api = mocker.MagicMock()
    cl.sync_api()
    assert cl.call_api.call_count == 0


def test_Client_sync_api(homedir, config, mocker):
    """
    Sync the API is authenticated.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.authenticated = mocker.MagicMock(return_value=True)
    cl.call_api = mocker.MagicMock()
    cl.sync_api()
    cl.call_api.assert_called_once_with(storage.get_remote_data, cl.on_synced,
                                        cl.on_sync_timeout, cl.api)


def test_Client_on_synced_remove_stale_sources(homedir, config, mocker):
    """
    On an API sync, if a source no longer exists, remove it from the GUI.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_source_id = 'abc123'
    mock_conv_wrapper = 'mock'

    gui = mocker.Mock()
    gui.conversations = {mock_source_id: mock_conv_wrapper}

    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', gui, mock_session, homedir)

    mock_source = mocker.Mock()
    mock_source.uuid = mock_source_id

    # not that the first item does *not* have the mock_source
    api_res = ([], mocker.MagicMock(), mocker.MagicMock())
    cl.on_synced(api_res)

    # check that the uuid is not longer in the dict
    assert mock_source_id not in gui.conversations


def test_Client_last_sync_with_file(homedir, config, mocker):
    """
    The flag indicating the time of the last sync with the API is stored in a
    dotfile in the user's home directory. If such a file exists, ensure an
    "arrow" object (representing the date/time) is returned.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    timestamp = '2018-10-10 18:17:13+01:00'
    mocker.patch("builtins.open", mocker.mock_open(read_data=timestamp))
    result = cl.last_sync()
    assert isinstance(result, arrow.Arrow)
    assert result.format() == timestamp


def test_Client_last_sync_no_file(homedir, config, mocker):
    """
    If there's no sync file, then just return None.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    mocker.patch("builtins.open", mocker.MagicMock(side_effect=Exception()))
    assert cl.last_sync() is None


def test_Client_on_synced_no_result(homedir, config, mocker):
    """
    If there's no result to syncing, then don't attempt to update local storage
    and perhaps implement some as-yet-undefined UI update.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.update_sources = mocker.MagicMock()
    result_data = Exception('Boom')  # Not the expected tuple.
    mock_storage = mocker.patch('securedrop_client.logic.storage')
    cl.on_synced(result_data)
    assert mock_storage.update_local_storage.call_count == 0
    cl.update_sources.assert_called_once_with()


def test_Client_on_synced_with_result(homedir, config, mocker):
    """
    If there's a result to syncing, then update local storage.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.update_sources = mocker.MagicMock()
    cl.api_runner = mocker.MagicMock()
    cl.gpg = mocker.MagicMock()

    result_data = ('sources', 'submissions', 'replies')

    cl.update_sources = mocker.MagicMock()
    cl.api_runner = mocker.MagicMock()

    mock_source = mocker.MagicMock()
    mock_source.key = {
        'type': 'PGP',
        'public': PUB_KEY,
    }

    mock_sources = [mock_source]

    result_data = (mock_sources, 'submissions', 'replies')

    cl.call_reset = mocker.MagicMock()
    mock_storage = mocker.patch('securedrop_client.logic.storage')
    cl.on_synced(result_data)
    mock_storage.update_local_storage. \
        assert_called_once_with(mock_session, mock_sources, "submissions",
                                "replies",
                                os.path.join(homedir, 'data'))

    cl.update_sources.assert_called_once_with()


def test_Client_on_synced_with_non_pgp_key(homedir, config, mocker):
    """
    If there's a result to syncing, then update local storage.
    This is it to check that we can gracefully handle missing keys.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.update_sources = mocker.MagicMock()
    cl.api_runner = mocker.MagicMock()

    mock_source = mocker.MagicMock()
    mock_source.key = {
        'type': 'PGP',
    }

    mock_sources = [mock_source]
    result_data = (mock_sources, 'submissions', 'replies')

    cl.call_reset = mocker.MagicMock()
    mock_storage = mocker.patch('securedrop_client.logic.storage')
    cl.on_synced(result_data)
    mock_storage.update_local_storage. \
        assert_called_once_with(mock_session, mock_sources, "submissions",
                                "replies",
                                os.path.join(homedir, 'data'))
    cl.update_sources.assert_called_once_with()


def test_Client_on_synced_with_key_import_fail(homedir, config, mocker):
    """
    If there's a result to syncing, then update local storage.
    This is it to check that we can gracefully handle an import failure.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.update_sources = mocker.MagicMock()
    cl.api_runner = mocker.MagicMock()

    mock_source = mocker.MagicMock()
    mock_source.key = {
        'type': 'PGP',
        'public': PUB_KEY,
    }

    mock_sources = [mock_source]
    result_data = (mock_sources, 'submissions', 'replies')

    cl.call_reset = mocker.MagicMock()
    mock_storage = mocker.patch('securedrop_client.logic.storage')
    mocker.patch.object(cl.gpg, 'import_key', side_effect=CryptoError)
    cl.on_synced(result_data)
    mock_storage.update_local_storage. \
        assert_called_once_with(mock_session, mock_sources, "submissions",
                                "replies",
                                os.path.join(homedir, 'data'))
    cl.update_sources.assert_called_once_with()


def test_Client_update_sync(homedir, config, mocker):
    """
    Cause the UI to update with the result of self.last_sync().
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.last_sync = mocker.MagicMock()
    cl.update_sync()
    assert cl.last_sync.call_count == 1
    cl.gui.show_sync.assert_called_once_with(cl.last_sync())


def test_Client_update_sources(homedir, config, mocker):
    """
    Ensure the UI displays a list of the available sources from local data
    store.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    mock_storage = mocker.patch('securedrop_client.logic.storage')
    source_list = [factory.Source(last_updated=2), factory.Source(last_updated=1)]
    mock_storage.get_local_sources.return_value = source_list
    cl.update_sources()
    mock_storage.get_local_sources.assert_called_once_with(mock_session)
    mock_gui.show_sources.assert_called_once_with(source_list)


def test_Client_update_conversation_views(homedir, config, mocker):
    """
    Ensure the UI displays the latest version of the messages/replies that
    have been downloaded/decrypted in the current conversation view.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.Mock()
    mock_conversation_wrapper = mocker.Mock()
    mock_conversation = mocker.MagicMock()
    mock_conversation_wrapper.conversation = mock_conversation
    mock_update_conversation = mocker.MagicMock()
    mock_conversation.update_conversation = mock_update_conversation
    mock_gui.conversations = {'foo': mock_conversation_wrapper}
    mock_session = mocker.MagicMock()

    # Since we use the set-like behavior of self.session
    # to check if the source is still persistent, let's mock that here
    mock_session.__contains__ = mocker.Mock()
    mock_session.__contains__.return_value = True

    mock_session.refresh = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.update_conversation_views()
    assert mock_session.refresh.called
    assert mock_update_conversation.called


def test_Client_unstars_a_source_if_starred(homedir, config, mocker):
    """
    Ensure that the client unstars a source if it is starred.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)

    source_db_object = mocker.MagicMock()
    source_db_object.uuid = mocker.MagicMock()
    source_db_object.is_starred = True

    cl.call_api = mocker.MagicMock()
    cl.api = mocker.MagicMock()
    cl.api.remove_star = mocker.MagicMock()
    cl.on_update_star_complete = mocker.MagicMock()
    cl.on_sidebar_action_timeout = mocker.MagicMock()

    source_sdk_object = mocker.MagicMock()
    mock_source = mocker.patch('sdclientapi.Source')
    mock_source.return_value = source_sdk_object
    cl.update_star(source_db_object)

    cl.call_api.assert_called_once_with(
        cl.api.remove_star, cl.on_update_star_complete,
        cl.on_sidebar_action_timeout, source_sdk_object)
    mock_gui.clear_error_status.assert_called_once_with()


def test_Client_unstars_a_source_if_unstarred(homedir, config, mocker):
    """
    Ensure that the client stars a source if it is unstarred.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    source_db_object = mocker.MagicMock()
    source_db_object.uuid = mocker.MagicMock()
    source_db_object.is_starred = False
    cl.call_api = mocker.MagicMock()
    cl.api = mocker.MagicMock()
    cl.api.add_star = mocker.MagicMock()
    cl.on_update_star_complete = mocker.MagicMock()
    cl.on_sidebar_action_timeout = mocker.MagicMock()
    source_sdk_object = mocker.MagicMock()
    mock_source = mocker.patch('sdclientapi.Source')
    mock_source.return_value = source_sdk_object
    cl.update_star(source_db_object)
    cl.call_api.assert_called_once_with(
        cl.api.add_star, cl.on_update_star_complete,
        cl.on_sidebar_action_timeout, source_sdk_object)
    mock_gui.clear_error_status.assert_called_once_with()


def test_Client_update_star_not_logged_in(homedir, config, mocker):
    """
    Ensure that starring/unstarring a source when not logged in calls
    the method that displays an error status in the left sidebar.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    source_db_object = mocker.MagicMock()
    cl.on_action_requiring_login = mocker.MagicMock()
    cl.api = None
    cl.update_star(source_db_object)
    cl.on_action_requiring_login.assert_called_with()


def test_Client_sidebar_action_timeout(homedir, config, mocker):
    """
    Show on error status sidebar that a timeout occurred.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.on_sidebar_action_timeout()
    mock_gui.update_error_status.assert_called_once_with(
        'The connection to the SecureDrop server timed out. Please try again.')


def test_Client_on_update_star_success(homedir, config, mocker):
    """
    If the starring occurs successfully, then a sync should occur to update
    locally.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    result = True
    cl.call_reset = mocker.MagicMock()
    cl.sync_api = mocker.MagicMock()
    cl.on_update_star_complete(result)
    cl.sync_api.assert_called_once_with()
    mock_gui.clear_error_status.assert_called_once_with()


def test_Client_on_update_star_failed(homedir, config, mocker):
    """
    If the starring does not occur properly, then an error should appear
    on the error status sidebar, and a sync will not occur.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    result = Exception('boom')
    cl.call_reset = mocker.MagicMock()
    cl.sync_api = mocker.MagicMock()
    cl.on_update_star_complete(result)
    cl.sync_api.assert_not_called()
    mock_gui.update_error_status.assert_called_once_with(
        'Failed to apply change.')


def test_Client_logout(homedir, config, mocker):
    """
    The API is reset to None and the UI is set to logged out state.
    The message and reply threads should also have the
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.api = mocker.MagicMock()
    cl.message_sync = mocker.MagicMock()
    cl.reply_sync = mocker.MagicMock()
    cl.message_sync.api = mocker.MagicMock()
    cl.reply_sync.api = mocker.MagicMock()
    cl.logout()
    assert cl.api is None
    assert cl.message_sync.api is None
    assert cl.reply_sync.api is None
    cl.gui.logout.assert_called_once_with()


def test_Client_set_activity_status(homedir, config, mocker):
    """
    Ensure the GUI set_status API is called.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.set_status("Hello, World!", 1000)
    mock_gui.update_activity_status.assert_called_once_with("Hello, World!", 1000)


PERMISSIONS_CASES = [
    {
        'should_pass': True,
        'home_perms': None,
    },
    {
        'should_pass': True,
        'home_perms': 0o0700,
    },
    {
        'should_pass': False,
        'home_perms': 0o0740,
    },
    {
        'should_pass': False,
        'home_perms': 0o0704,
    },
]


def test_create_client_dir_permissions(tmpdir, mocker):
    '''
    Check that creating an app behaves appropriately with different
    permissions on the various directories needed for it to function.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    # we can't rely on the config fixture, and because of the order of exectution,
    # we can't create the config at the right time, we we have to mock both
    # `open` and `json.loads`
    mock_open = mocker.patch('securedrop_client.config.open')
    mock_json = mocker.patch('securedrop_client.config.json.loads')

    for idx, case in enumerate(PERMISSIONS_CASES):
        sdc_home = os.path.join(str(tmpdir), 'case-{}'.format(idx))

        # optionally create the dir
        if case['home_perms'] is not None:
            os.mkdir(sdc_home, case['home_perms'])

        def func() -> None:
            Client('http://localhost', mock_gui, mock_session, sdc_home)

        if case['should_pass']:
            func()
        else:
            with pytest.raises(RuntimeError):
                func()

    # check that both mocks were called to ensure they aren't "dead code"
    assert mock_open.called
    assert mock_json.called


def test_Client_on_file_download_Submission(homedir, config, mocker):
    """
    If the handler is passed a submission, check the download_submission
    function is the one called against the API.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    source = factory.Source()
    file_ = db.File(source=source, uuid='uuid', size=1234, filename='1-myfile.doc.gpg',
                    download_url='http://myserver/myfile', is_downloaded=False)
    cl.call_api = mocker.MagicMock()
    cl.api = mocker.MagicMock()
    submission_sdk_object = mocker.MagicMock()
    mock_submission = mocker.patch('sdclientapi.Submission')
    mock_submission.return_value = submission_sdk_object
    cl.on_file_download(source, file_)
    cl.call_api.assert_called_once_with(
        cl.api.download_submission, cl.on_file_downloaded,
        cl.on_download_timeout, submission_sdk_object,
        cl.data_dir, current_object=file_)


def test_Client_on_file_downloaded_success(homedir, config, mocker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.update_sources = mocker.MagicMock()
    cl.api_runner = mocker.MagicMock()
    cl.file_ready = mocker.MagicMock()  # signal when file is downloaded
    test_filename = "1-my-file-location-msg.gpg"
    test_object_uuid = 'uuid-of-downloaded-object'
    cl.call_reset = mocker.MagicMock()
    result_data = ('this-is-a-sha256-sum', test_filename)
    submission_db_object = mocker.MagicMock()
    submission_db_object.uuid = test_object_uuid
    submission_db_object.filename = test_filename
    mock_storage = mocker.patch('securedrop_client.logic.storage')
    mock_gpg = mocker.patch.object(cl.gpg, 'decrypt_submission_or_reply', return_value='filepath')
    mocker.patch('shutil.move')
    cl.on_file_downloaded(result_data, current_object=submission_db_object)
    mock_gpg.call_count == 1
    mock_storage.mark_file_as_downloaded.assert_called_once_with(
        test_object_uuid, mock_session)
    mock_storage.set_object_decryption_status_with_content.assert_called_once_with(
        submission_db_object, mock_session, True)

    # Signal should be emitted with UUID of the successfully downloaded object
    cl.file_ready.emit.assert_called_once_with(test_object_uuid)


def test_Client_on_file_downloaded_api_failure(homedir, config, mocker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.file_ready = mocker.MagicMock()  # signal when file is downloaded
    cl.update_sources = mocker.MagicMock()
    cl.api_runner = mocker.MagicMock()
    test_filename = "1-my-file-location-msg.gpg"
    cl.api_runner.result = ("", test_filename)
    cl.call_reset = mocker.MagicMock()
    cl.set_status = mocker.MagicMock()
    result_data = Exception('error message')
    submission_db_object = mocker.MagicMock()
    submission_db_object.uuid = 'myuuid'
    submission_db_object.filename = 'filename'
    cl.on_file_downloaded(result_data, current_object=submission_db_object)
    cl.set_status.assert_called_once_with(
        "The file download failed. Please try again.")
    cl.file_ready.emit.assert_not_called()


def test_Client_on_file_downloaded_decrypt_failure(homedir, config, mocker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.update_sources = mocker.MagicMock()
    cl.api_runner = mocker.MagicMock()
    cl.file_ready = mocker.MagicMock()  # signal when file is downloaded
    test_filename = "1-my-file-location-msg.gpg"
    cl.api_runner.result = ("", test_filename)
    cl.set_status = mocker.MagicMock()
    result_data = ('this-is-a-sha256-sum', test_filename)
    submission_db_object = mocker.MagicMock()
    submission_db_object.uuid = 'myuuid'
    submission_db_object.filename = 'filename'
    mock_gpg = mocker.patch.object(cl.gpg, 'decrypt_submission_or_reply',
                                   side_effect=CryptoError())
    mock_storage = mocker.patch('securedrop_client.logic.storage')
    mocker.patch('shutil.move')

    cl.on_file_downloaded(result_data, current_object=submission_db_object)
    mock_gpg.call_count == 1
    cl.set_status.assert_called_once_with(
        "Failed to decrypt file, please try again or talk to your administrator.")
    mock_storage.set_object_decryption_status_with_content.assert_called_once_with(
        submission_db_object, mock_session, False)
    cl.file_ready.emit.assert_not_called()


def test_Client_on_file_download_user_not_signed_in(homedir, config, mocker):
    """
    If a user clicks the download button but is not logged in,
    an error should appear.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    source = factory.Source()
    file_ = db.File(source=source, uuid='uuid', size=1234, filename='1-myfile.doc.gpg',
                    download_url='http://myserver/myfile', is_downloaded=False)
    cl.on_action_requiring_login = mocker.MagicMock()
    cl.api = None
    submission_sdk_object = mocker.MagicMock()
    mock_submission = mocker.patch('sdclientapi.Submission')
    mock_submission.return_value = submission_sdk_object
    cl.on_file_download(source, file_)
    cl.on_action_requiring_login.assert_called_once_with()


def test_Client_on_download_timeout(homedir, config, mocker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.update_sources = mocker.MagicMock()
    cl.api_runner = mocker.MagicMock()
    current_object = mocker.MagicMock()
    test_filename = "1-my-file-location-msg.gpg"
    cl.api_runner.result = ("", test_filename)
    cl.call_reset = mocker.MagicMock()
    cl.set_status = mocker.MagicMock()
    cl.on_download_timeout(current_object)
    cl.set_status.assert_called_once_with(
        "The connection to the SecureDrop server timed out. Please try again.")


def test_Client_on_file_download_Reply(homedir, config, mocker):
    """
    If the handler is passed a reply, check the download_reply
    function is the one called against the API.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    source = factory.Source()
    journalist = db.User('Testy mcTestface')
    reply = db.Reply(uuid='reply-uuid',
                     journalist=journalist,
                     source=source,
                     filename='1-my-reply.gpg',
                     size=123)  # Not a sdclientapi.Submission
    cl.call_api = mocker.MagicMock()
    cl.api = mocker.MagicMock()
    reply_sdk_object = mocker.MagicMock()
    mock_reply = mocker.patch('sdclientapi.Reply')
    mock_reply.return_value = reply_sdk_object
    cl.on_file_download(source, reply)
    cl.call_api.assert_called_once_with(cl.api.download_reply,
                                        cl.on_file_downloaded,
                                        cl.on_download_timeout,
                                        reply_sdk_object,
                                        cl.data_dir, current_object=reply)


def test_Client_on_file_open(homedir, config, mocker):
    """
    If running on Qubes, a new QProcess with the expected command and args
    should be started.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.proxy = True
    mock_submission = mocker.MagicMock()
    mock_submission.filename = '1-test.pdf'
    mock_subprocess = mocker.MagicMock()
    mock_process = mocker.MagicMock(return_value=mock_subprocess)
    mocker.patch('securedrop_client.logic.QProcess', mock_process)
    cl.on_file_open(mock_submission)
    mock_process.assert_called_once_with(cl)
    mock_subprocess.start.call_count == 1


def test_Client_on_delete_action_timeout(homedir, config, mocker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl._on_delete_action_timeout()
    message = 'The connection to SecureDrop timed out. Please try again.'
    cl.gui.update_error_status.assert_called_with(message)


def test_Client_on_delete_source_complete_with_results(homedir, config, mocker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.sync_api = mocker.MagicMock()
    cl._on_delete_source_complete(True)
    cl.sync_api.assert_called_with()
    cl.gui.clear_error_status.assert_called_with()


def test_Client_on_delete_source_complete_without_results(homedir, config, mocker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl._on_delete_source_complete(False)
    cl.gui.update_error_status.assert_called_with('Failed to delete source at server')


def test_Client_delete_source(homedir, config, mocker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.call_api = mocker.MagicMock()
    cl.api = mocker.MagicMock()
    cl.delete_source(mock_source)
    cl.call_api.assert_called_with(
        cl.api.delete_source,
        cl._on_delete_source_complete,
        cl._on_delete_action_timeout,
        mock_source
    )


def test_Client_send_reply_success(homedir, mocker):
    '''
    Check that the "happy path" of encrypting a message and sending it to the sever behaves as
    expected.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    cl = Client('http://localhost', mock_gui, mock_session, homedir)

    cl.call_api = mocker.Mock()
    cl.api = mocker.Mock()
    encrypted_reply = 's3kr1t m3ss1dg3'
    mock_encrypt = mocker.patch.object(cl.gpg, 'encrypt_to_source', return_value=encrypted_reply)
    source_uuid = 'abc123'
    msg_uuid = 'xyz456'
    msg = 'wat'
    mock_sdk_source = mocker.Mock()
    mock_source_init = mocker.patch('securedrop_client.logic.sdclientapi.Source',
                                    return_value=mock_sdk_source)

    cl.send_reply(source_uuid, msg_uuid, msg)

    # ensure message is encrypted
    mock_encrypt.assert_called_once_with(source_uuid, msg)

    # ensure api is called
    cl.call_api.assert_called_once_with(
        cl.api.reply_source,
        cl._on_reply_complete,
        cl._on_reply_timeout,
        mock_sdk_source,
        encrypted_reply,
        msg_uuid,
        current_object=(source_uuid, msg_uuid),
    )

    assert mock_source_init.called  # to prevent stale mocks


def test_Client_send_reply_gpg_error(homedir, mocker):
    '''
    Check that if gpg fails when sending a message, we alert the UI and do *not* call the API.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    cl = Client('http://localhost', mock_gui, mock_session, homedir)

    cl.call_api = mocker.Mock()
    cl.api = mocker.Mock()
    mock_encrypt = mocker.patch.object(cl.gpg, 'encrypt_to_source', side_effect=Exception)
    source_uuid = 'abc123'
    msg_uuid = 'xyz456'
    msg = 'wat'
    mock_sdk_source = mocker.Mock()
    mock_source_init = mocker.patch('securedrop_client.logic.sdclientapi.Source',
                                    return_value=mock_sdk_source)
    mock_reply_failed = mocker.patch.object(cl, 'reply_failed')

    cl.send_reply(source_uuid, msg_uuid, msg)

    # ensure there is an attempt to encrypt the message
    mock_encrypt.assert_called_once_with(source_uuid, msg)

    # ensure we emit a failure on gpg errors
    mock_reply_failed.emit.assert_called_once_with(msg_uuid)

    # ensure api not is called after a gpg error
    assert not cl.call_api.called

    assert mock_source_init.called  # to prevent stale mocks


def test_Client_on_reply_complete_success(homedir, mocker):
    '''
    Check that when the result is a success, the client emits the correct signal.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_reply_init = mocker.patch('securedrop_client.logic.db.Reply')

    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.api = mocker.Mock()
    journalist_uuid = 'abc123'
    cl.api.token = {'journalist_uuid': journalist_uuid}
    mock_reply_succeeded = mocker.patch.object(cl, 'reply_succeeded')
    mock_reply_failed = mocker.patch.object(cl, 'reply_failed')

    reply = sdlocalobjects.Reply(uuid='xyz456', filename='1-wat.gpg')

    source_uuid = 'foo111'
    msg_uuid = 'bar222'
    current_object = (source_uuid, msg_uuid)
    cl._on_reply_complete(reply, current_object)
    cl.session.commit.assert_called_once_with()
    mock_reply_succeeded.emit.assert_called_once_with(msg_uuid)
    assert not mock_reply_failed.emit.called

    assert mock_reply_init.called  # to prevent stale mocks


def test_Client_on_reply_complete_failure(homedir, mocker):
    '''
    Check that when the result is a failure, the client emits the correct signal.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.api = mocker.Mock()
    journalist_uuid = 'abc123'
    cl.api.token = {'journalist_uuid': journalist_uuid}
    mock_reply_succeeded = mocker.patch.object(cl, 'reply_succeeded')
    mock_reply_failed = mocker.patch.object(cl, 'reply_failed')

    source_uuid = 'foo111'
    msg_uuid = 'bar222'
    current_object = (source_uuid, msg_uuid)
    cl._on_reply_complete(Exception, current_object)
    mock_reply_failed.emit.assert_called_once_with(msg_uuid)
    assert not mock_reply_succeeded.emit.called


def test_Client_on_reply_timeout(homedir, mocker):
    '''
    Check that when the reply timesout, the correct signal is emitted.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    cl.api = mocker.Mock()
    journalist_uuid = 'abc123'
    cl.api.token = {'journalist_uuid': journalist_uuid}
    mock_reply_succeeded = mocker.patch.object(cl, 'reply_succeeded')
    mock_reply_failed = mocker.patch.object(cl, 'reply_failed')

    source_uuid = 'foo111'
    msg_uuid = 'bar222'
    current_object = (source_uuid, msg_uuid)
    cl._on_reply_timeout(current_object)
    mock_reply_failed.emit.assert_called_once_with(msg_uuid)
    assert not mock_reply_succeeded.emit.called


def test_Client_is_authenticated_property(homedir, mocker):
    '''
    Check that the @property `is_authenticated`:
      - Cannot be deleted
      - Emits the correct signals when updated
      - Sets internal state to ensure signals are only set when the state changes
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    cl = Client('http://localhost', mock_gui, mock_session, homedir)
    mock_signal = mocker.patch.object(cl, 'authentication_state')

    # default state is unauthenticated
    assert cl.is_authenticated is False

    # the property cannot be deleted
    with pytest.raises(AttributeError):
        del cl.is_authenticated

    # setting the signal to its current value does not fire the signal
    cl.is_authenticated = False
    assert not mock_signal.emit.called
    assert cl.is_authenticated is False

    # setting the property to True sends a signal
    cl.is_authenticated = True
    mock_signal.emit.assert_called_once_with(True)
    assert cl.is_authenticated is True

    mock_signal.reset_mock()

    cl.is_authenticated = False
    mock_signal.emit.assert_called_once_with(False)
    assert cl.is_authenticated is False
