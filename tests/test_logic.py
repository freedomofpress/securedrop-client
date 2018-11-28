"""
Make sure the Client object, containing the application logic, behaves as
expected.
"""
import arrow
import os
import pytest
from tests import factory
from securedrop_client import storage, models
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


def test_Client_init(safe_tmpdir, config, mocker):
    """
    The passed in gui, app and session instances are correctly referenced and,
    where appropriate, have a reference back to the client.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost/', mock_gui, mock_session, str(safe_tmpdir))
    assert cl.hostname == 'http://localhost/'
    assert cl.gui == mock_gui
    assert cl.session == mock_session
    assert cl.api_threads == {}


def test_Client_setup(safe_tmpdir, config, mocker):
    """
    Ensure the application is set up with the following default state:
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.update_sources = mocker.MagicMock()
    cl.setup()
    cl.gui.setup.assert_called_once_with(cl)
    cl.update_sources.assert_called_once_with()
    cl.gui.show_login.assert_called_once_with()


def test_Client_start_message_thread(safe_tmpdir, config, mocker):
    """
    When starting message-fetching thread, make sure we do a few things.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    mock_qthread = mocker.patch('securedrop_client.logic.QThread')
    mocker.patch('securedrop_client.logic.MessageSync')
    cl.message_sync = mocker.MagicMock()
    cl.start_message_thread()
    cl.message_sync.moveToThread.assert_called_once_with(mock_qthread())
    cl.message_thread.started.connect.assert_called_once_with(cl.message_sync.run)
    cl.message_thread.start.assert_called_once_with()


def test_Client_start_message_thread_if_already_running(safe_tmpdir, config, mocker):
    """
    Ensure that when starting the message thread, we don't start another thread
    if it's already running. Instead, we just authenticate the existing thread.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.api = 'api object'
    cl.message_sync = mocker.MagicMock()
    cl.message_thread = mocker.MagicMock()
    cl.message_thread.api = None
    cl.start_message_thread()
    cl.message_sync.api = cl.api
    cl.message_thread.start.assert_not_called()


def test_Client_start_reply_thread(safe_tmpdir, config, mocker):
    """
    When starting reply-fetching thread, make sure we do a few things.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    mock_qthread = mocker.patch('securedrop_client.logic.QThread')
    mocker.patch('securedrop_client.logic.ReplySync')
    cl.reply_sync = mocker.MagicMock()
    cl.start_reply_thread()
    cl.reply_sync.moveToThread.assert_called_once_with(mock_qthread())
    cl.reply_thread.started.connect.assert_called_once_with(
        cl.reply_sync.run)
    cl.reply_thread.start.assert_called_once_with()


def test_Client_start_reply_thread_if_already_running(safe_tmpdir, config, mocker):
    """
    Ensure that when starting the reply thread, we don't start another thread
    if it's already running. Instead, we just authenticate the existing thread.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.api = 'api object'
    cl.reply_sync = mocker.MagicMock()
    cl.reply_thread = mocker.MagicMock()
    cl.reply_thread.api = None
    cl.start_reply_thread()
    cl.reply_sync.api = cl.api
    cl.reply_thread.start.assert_not_called()


def test_Client_call_api(safe_tmpdir, config, mocker):
    """
    A new thread and APICallRunner is created / setup.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
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


def test_Client_clean_thread_no_thread(safe_tmpdir, config, mocker):
    """
    The client will ignore an attempt to reset an API call if there's no such
    call "in flight".
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.finish_api_call = mocker.MagicMock()
    cl.api_threads = {'a': 'b'}
    cl.clean_thread('foo')
    assert len(cl.api_threads) == 1


def test_Client_clean_thread(safe_tmpdir, config, mocker):
    """
    Cleaning up an existing thread disconnects the timer and removes it from
    the api_threads collection.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    mock_timer = mocker.MagicMock()
    cl.api_threads = {
        'foo': {
            'timer': mock_timer,
        }
    }
    cl.clean_thread('foo')
    assert mock_timer.disconnect.call_count == 1
    assert 'foo' not in cl.api_threads


def test_Client_login(safe_tmpdir, config, mocker):
    """
    Ensures the API is called in the expected manner for logging in the user
    given the username, password and 2fa token.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.call_api = mocker.MagicMock()
    mock_api = mocker.patch('securedrop_client.logic.sdclientapi.API')
    cl.login('username', 'password', '123456')
    cl.call_api.assert_called_once_with(mock_api().authenticate,
                                        cl.on_authenticate,
                                        cl.on_login_timeout)


def test_Client_on_authenticate_failed(safe_tmpdir, config, mocker):
    """
    If the server responds with a negative to the request to authenticate, make
    sure the user knows.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    result_data = 'false'
    cl.on_authenticate(result_data)
    mock_gui.show_login_error.\
        assert_called_once_with(error='There was a problem signing in. Please '
                                'verify your credentials and try again.')


def test_Client_on_authenticate_ok(safe_tmpdir, config, mocker):
    """
    Ensure the client syncs when the user successfully logs in.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.sync_api = mocker.MagicMock()
    cl.api = mocker.MagicMock()
    cl.start_message_thread = mocker.MagicMock()
    cl.start_reply_thread = mocker.MagicMock()
    cl.api.username = 'test'
    cl.on_authenticate(True)
    cl.sync_api.assert_called_once_with()
    cl.start_message_thread.assert_called_once_with()
    cl.gui.set_logged_in_as.assert_called_once_with('test')
    # Error status bar should be cleared
    cl.gui.update_error_status.assert_called_once_with("")


def test_Client_completed_api_call_without_current_object(safe_tmpdir, config, mocker):
    """
    Ensure that cleanup is performed if an API call returns in the expected
    time.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
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


def test_Client_completed_api_call_with_current_object(safe_tmpdir, config, mocker):
    """
    Ensure that cleanup is performed if an API call returns in the expected
    time.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
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


def test_Client_timeout_cleanup_without_current_object(safe_tmpdir, config, mocker):
    """
    Ensure that cleanup is performed if an API call times out.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
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


def test_Client_timeout_cleanup_with_current_object(safe_tmpdir, config, mocker):
    """
    Ensure that cleanup is performed if an API call times out.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
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


def test_Client_on_sync_timeout(safe_tmpdir, config, mocker):
    """
    Display error message in status bar if sync times out.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.api = "this is populated"
    cl.on_sync_timeout()
    assert cl.api is not None
    mock_gui.update_error_status.\
        assert_called_once_with(error='The connection to the SecureDrop '
                                'server timed out. Please try again.')


def test_Client_on_login_timeout(safe_tmpdir, config, mocker):
    """
    Reset the form if the API call times out.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.call_reset = mocker.MagicMock()
    cl.on_login_timeout()
    assert cl.api is None
    mock_gui.show_login_error.\
        assert_called_once_with(error='The connection to the SecureDrop '
                                'server timed out. Please try again.')


def test_Client_on_action_requiring_login(safe_tmpdir, config, mocker):
    """
    Ensure that when on_action_requiring_login is called, an error
    is shown in the GUI status area.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.on_action_requiring_login()
    mock_gui.update_error_status.assert_called_once_with(
        'You must sign in to perform this action.')


def test_Client_authenticated_yes(safe_tmpdir, config, mocker):
    """
    If the API is authenticated return True.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.api = mocker.MagicMock()
    cl.api.token = {'token': 'foo'}
    assert cl.authenticated() is True


def test_Client_authenticated_no(safe_tmpdir, config, mocker):
    """
    If the API is authenticated return True.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.api = mocker.MagicMock()
    cl.api.token = {'token': ''}
    assert cl.authenticated() is False


def test_Client_authenticated_no_api(safe_tmpdir, config, mocker):
    """
    If the API is authenticated return True.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.api = None
    assert cl.authenticated() is False


def test_Client_sync_api_not_authenticated(safe_tmpdir, config, mocker):
    """
    If the API isn't authenticated, don't sync.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.authenticated = mocker.MagicMock(return_value=False)
    cl.call_api = mocker.MagicMock()
    cl.sync_api()
    assert cl.call_api.call_count == 0


def test_Client_sync_api(safe_tmpdir, config, mocker):
    """
    Sync the API is authenticated.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.authenticated = mocker.MagicMock(return_value=True)
    cl.call_api = mocker.MagicMock()
    cl.sync_api()
    cl.call_api.assert_called_once_with(storage.get_remote_data, cl.on_synced,
                                        cl.on_sync_timeout, cl.api)


def test_Client_last_sync_with_file(safe_tmpdir, config, mocker):
    """
    The flag indicating the time of the last sync with the API is stored in a
    dotfile in the user's home directory. If such a file exists, ensure an
    "arrow" object (representing the date/time) is returned.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    timestamp = '2018-10-10 18:17:13+01:00'
    mocker.patch("builtins.open", mocker.mock_open(read_data=timestamp))
    result = cl.last_sync()
    assert isinstance(result, arrow.Arrow)
    assert result.format() == timestamp


def test_Client_last_sync_no_file(safe_tmpdir, config, mocker):
    """
    If there's no sync file, then just return None.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    mocker.patch("builtins.open", mocker.MagicMock(side_effect=Exception()))
    assert cl.last_sync() is None


def test_Client_on_synced_no_result(safe_tmpdir, config, mocker):
    """
    If there's no result to syncing, then don't attempt to update local storage
    and perhaps implement some as-yet-undefined UI update.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.update_sources = mocker.MagicMock()
    result_data = Exception('Boom')  # Not the expected tuple.
    mock_storage = mocker.patch('securedrop_client.logic.storage')
    cl.on_synced(result_data)
    assert mock_storage.update_local_storage.call_count == 0
    cl.update_sources.assert_called_once_with()


def test_Client_on_synced_with_result(safe_tmpdir, config, mocker):
    """
    If there's a result to syncing, then update local storage.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
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
                                os.path.join(str(safe_tmpdir), 'data'))

    cl.update_sources.assert_called_once_with()


def test_Client_on_synced_with_non_pgp_key(safe_tmpdir, config, mocker):
    """
    If there's a result to syncing, then update local storage.
    This is it to check that we can gracefully handle missing keys.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
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
                                os.path.join(str(safe_tmpdir), 'data'))
    cl.update_sources.assert_called_once_with()


def test_Client_on_synced_with_key_import_fail(safe_tmpdir, config, mocker):
    """
    If there's a result to syncing, then update local storage.
    This is it to check that we can gracefully handle an import failure.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
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
                                os.path.join(str(safe_tmpdir), 'data'))
    cl.update_sources.assert_called_once_with()


def test_Client_update_sync(safe_tmpdir, config, mocker):
    """
    Cause the UI to update with the result of self.last_sync().
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.last_sync = mocker.MagicMock()
    cl.update_sync()
    assert cl.last_sync.call_count == 1
    cl.gui.show_sync.assert_called_once_with(cl.last_sync())


def test_Client_update_sources(safe_tmpdir, config, mocker):
    """
    Ensure the UI displays a list of the available sources from local data
    store.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    mock_storage = mocker.patch('securedrop_client.logic.storage')
    source_list = [factory.Source(last_updated=2), factory.Source(last_updated=1)]
    mock_storage.get_local_sources.return_value = source_list
    cl.update_sources()
    mock_storage.get_local_sources.assert_called_once_with(mock_session)
    mock_gui.show_sources.assert_called_once_with(source_list)


def test_Client_update_conversation_view_current_source(safe_tmpdir, config, mocker):
    """
    Ensure the UI displays the latest version of the messages/replies that
    have been downloaded/decrypted in the current conversation view.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_gui.current_source = 'teehee'
    mock_gui.show_conversation_for = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    # Since we use the set-like behavior of self.session
    # to check if the source is still persistent, let's mock that here
    mock_session.__contains__ = mocker.MagicMock()
    mock_session.__contains__.return_value = [mock_gui.current_source]

    mock_session.refresh = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.update_conversation_view()
    mock_session.refresh.assert_called_with(mock_gui.current_source)
    mock_gui.show_conversation_for.assert_called_once_with(
        mock_gui.current_source)


def test_Client_update_conversation_deleted_source(safe_tmpdir, config, mocker):
    """
    Ensure the UI does not attempt to refresh and display a deleted
    source.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_gui.current_source = 'teehee'
    mock_gui.show_conversation_for = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_session.refresh = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.update_conversation_view()
    mock_session.refresh.assert_not_called()
    mock_gui.show_conversation_for.assert_not_called()


def test_Client_update_conversation_view_no_current_source(safe_tmpdir, config, mocker):
    """
    Ensure that if there is no current source (i.e. the user has not clicked
    a source in the sidebar), the UI will not redraw the conversation view.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_gui.current_source = None
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.update_conversation_view()
    mock_gui.show_conversation_for.assert_not_called()


def test_Client_unstars_a_source_if_starred(safe_tmpdir, config, mocker):
    """
    Ensure that the client unstars a source if it is starred.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
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
    mock_gui.update_error_status.assert_called_once_with("")


def test_Client_unstars_a_source_if_unstarred(safe_tmpdir, config, mocker):
    """
    Ensure that the client stars a source if it is unstarred.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
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
    mock_gui.update_error_status.assert_called_once_with("")


def test_Client_update_star_not_logged_in(safe_tmpdir, config, mocker):
    """
    Ensure that starring/unstarring a source when not logged in calls
    the method that displays an error status in the left sidebar.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    source_db_object = mocker.MagicMock()
    cl.on_action_requiring_login = mocker.MagicMock()
    cl.api = None
    cl.update_star(source_db_object)
    cl.on_action_requiring_login.assert_called_with()


def test_Client_sidebar_action_timeout(safe_tmpdir, config, mocker):
    """
    Show on error status sidebar that a timeout occurred.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.on_sidebar_action_timeout()
    mock_gui.update_error_status.assert_called_once_with(
        'The connection to the SecureDrop server timed out. Please try again.')


def test_Client_on_update_star_success(safe_tmpdir, config, mocker):
    """
    If the starring occurs successfully, then a sync should occur to update
    locally.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    result = True
    cl.call_reset = mocker.MagicMock()
    cl.sync_api = mocker.MagicMock()
    cl.on_update_star_complete(result)
    cl.sync_api.assert_called_once_with()
    mock_gui.update_error_status.assert_called_once_with("")


def test_Client_on_update_star_failed(safe_tmpdir, config, mocker):
    """
    If the starring does not occur properly, then an error should appear
    on the error status sidebar, and a sync will not occur.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    result = Exception('boom')
    cl.call_reset = mocker.MagicMock()
    cl.sync_api = mocker.MagicMock()
    cl.on_update_star_complete(result)
    cl.sync_api.assert_not_called()
    mock_gui.update_error_status.assert_called_once_with(
        'Failed to apply change.')


def test_Client_logout(safe_tmpdir, config, mocker):
    """
    The API is reset to None and the UI is set to logged out state.
    The message and reply threads should also have the
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
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


def test_Client_set_status(safe_tmpdir, config, mocker):
    """
    Ensure the GUI set_status API is called.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.set_status("Hello, World!", 1000)
    mock_gui.set_status.assert_called_once_with("Hello, World!", 1000)


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


def test_Client_on_file_download_Submission(safe_tmpdir, config, mocker):
    """
    If the handler is passed a submission, check the download_submission
    function is the one called against the API.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    source = factory.Source()
    submission = models.Submission(source, 'submission-uuid', 1234,
                                   'myfile.doc.gpg', 'http://myserver/myfile')
    cl.call_api = mocker.MagicMock()
    cl.api = mocker.MagicMock()
    submission_sdk_object = mocker.MagicMock()
    mock_submission = mocker.patch('sdclientapi.Submission')
    mock_submission.return_value = submission_sdk_object
    cl.on_file_download(source, submission)
    cl.call_api.assert_called_once_with(
        cl.api.download_submission, cl.on_file_downloaded,
        cl.on_download_timeout, submission_sdk_object,
        cl.data_dir, current_object=submission)


def test_Client_on_file_downloaded_success(safe_tmpdir, config, mocker):
    '''
    Using the `config` fixture to ensture the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.update_sources = mocker.MagicMock()
    cl.api_runner = mocker.MagicMock()
    test_filename = "my-file-location-msg.gpg"
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


def test_Client_on_file_downloaded_api_failure(safe_tmpdir, config, mocker):
    '''
    Using the `config` fixture to ensture the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.update_sources = mocker.MagicMock()
    cl.api_runner = mocker.MagicMock()
    test_filename = "my-file-location-msg.gpg"
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


def test_Client_on_file_downloaded_decrypt_failure(safe_tmpdir, config, mocker):
    '''
    Using the `config` fixture to ensture the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.update_sources = mocker.MagicMock()
    cl.api_runner = mocker.MagicMock()
    test_filename = "my-file-location-msg.gpg"
    cl.api_runner.result = ("", test_filename)
    cl.set_status = mocker.MagicMock()
    result_data = ('this-is-a-sha256-sum', test_filename)
    submission_db_object = mocker.MagicMock()
    submission_db_object.uuid = 'myuuid'
    submission_db_object.filename = 'filename'
    mock_gpg = mocker.patch.object(cl.gpg, 'decrypt_submission_or_reply',
                                   side_effect=CryptoError())
    mocker.patch('shutil.move')

    cl.on_file_downloaded(result_data, current_object=submission_db_object)
    mock_gpg.call_count == 1
    cl.set_status.assert_called_once_with(
        "Failed to download and decrypt file, please try again.")


def test_Client_on_file_download_user_not_signed_in(safe_tmpdir, config, mocker):
    """
    If a user clicks the download button but is not logged in,
    an error should appear.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    source = factory.Source()
    submission = models.Submission(source, 'submission-uuid', 1234,
                                   'myfile.doc.gpg', 'http://myserver/myfile')
    cl.on_action_requiring_login = mocker.MagicMock()
    cl.api = None
    submission_sdk_object = mocker.MagicMock()
    mock_submission = mocker.patch('sdclientapi.Submission')
    mock_submission.return_value = submission_sdk_object
    cl.on_file_download(source, submission)
    cl.on_action_requiring_login.assert_called_once_with()


def test_Client_on_download_timeout(safe_tmpdir, config, mocker):
    '''
    Using the `config` fixture to ensture the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.update_sources = mocker.MagicMock()
    cl.api_runner = mocker.MagicMock()
    current_object = mocker.MagicMock()
    test_filename = "my-file-location-msg.gpg"
    cl.api_runner.result = ("", test_filename)
    cl.call_reset = mocker.MagicMock()
    cl.set_status = mocker.MagicMock()
    cl.on_download_timeout(current_object)
    cl.set_status.assert_called_once_with(
        "The connection to the SecureDrop server timed out. Please try again.")


def test_Client_on_file_download_Reply(safe_tmpdir, config, mocker):
    """
    If the handler is passed a reply, check the download_reply
    function is the one called against the API.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    source = factory.Source()
    journalist = models.User('Testy mcTestface')
    reply = models.Reply('reply-uuid', journalist, source,
                         'my-reply.gpg', 123)  # Not a sdclientapi.Submission
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


def test_Client_on_object_loaded(safe_tmpdir, config, mocker):
    """
    Tests that the ORM "loaded" callback correctly configures the target object
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.on_object_loaded(cl, None)
    assert cl.data.data_dir == os.path.join(str(safe_tmpdir), "data")


def test_Client_on_file_open(safe_tmpdir, config, mocker):
    """
    If running on Qubes, a new QProcess with the expected command and args
    should be started.
    Using the `config` fixture to ensture the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.proxy = True
    mock_submission = mocker.MagicMock()
    mock_submission.filename = 'test.pdf'
    mock_subprocess = mocker.MagicMock()
    mock_process = mocker.MagicMock(return_value=mock_subprocess)
    mocker.patch('securedrop_client.logic.QProcess', mock_process)
    cl.on_file_open(mock_submission)
    mock_process.assert_called_once_with(cl)
    mock_subprocess.start.call_count == 1


def test_Client_on_delete_action_timeout(safe_tmpdir, config, mocker):
    '''
    Using the `config` fixture to ensture the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl._on_delete_action_timeout()
    message = 'The connection to SecureDrop timed out. Please try again.'
    cl.gui.update_error_status.assert_called_with(message)


def test_Client_on_delete_source_complete_with_results(safe_tmpdir, config, mocker):
    '''
    Using the `config` fixture to ensture the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.sync_api = mocker.MagicMock()
    cl._on_delete_source_complete(True)
    cl.sync_api.assert_called_with()
    cl.gui.update_error_status.assert_called_with("")


def test_Client_on_delete_source_complete_without_results(safe_tmpdir, config, mocker):
    '''
    Using the `config` fixture to ensture the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl._on_delete_source_complete(False)
    cl.gui.update_error_status.assert_called_with('Failed to delete source at server')


def test_Client_delete_source(safe_tmpdir, config, mocker):
    '''
    Using the `config` fixture to ensture the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.call_api = mocker.MagicMock()
    cl.api = mocker.MagicMock()
    cl.delete_source(mock_source)
    cl.call_api.assert_called_with(
        cl.api.delete_source,
        cl._on_delete_source_complete,
        cl._on_delete_action_timeout,
        mock_source
    )
