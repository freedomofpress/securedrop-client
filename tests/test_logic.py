"""
Make sure the Controller object, containing the application logic, behaves as
expected.
"""
import arrow
import os
import pytest

from sdclientapi import sdlocalobjects, RequestTimeoutError
from tests import factory
from securedrop_client import storage, db
from securedrop_client.crypto import CryptoError
from securedrop_client.logic import APICallRunner, Controller

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
    cr.call_succeeded = mocker.MagicMock()
    cr.call_api()
    assert cr.result == 'foo'
    cr.call_succeeded.emit.assert_called_once_with()


def test_APICallRunner_with_exception(mocker):
    """
    An exception has occured so emit False.
    """
    ex = Exception('boom')
    mock_api_call = mocker.MagicMock(side_effect=ex)
    mock_api_call.__name__ = 'my_function'
    mock_current_object = mocker.MagicMock()
    cr = APICallRunner(mock_api_call, mock_current_object, 'foo', bar='baz')
    cr.call_failed = mocker.MagicMock()
    mocker.patch('securedrop_client.logic.QTimer')
    cr.call_api()
    assert cr.result == ex
    cr.call_failed.emit.assert_called_once_with()


def test_Controller_init(homedir, config, mocker):
    """
    The passed in gui, app and session instances are correctly referenced and,
    where appropriate, have a reference back to the client.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost/', mock_gui, mock_session, homedir)
    assert co.hostname == 'http://localhost/'
    assert co.gui == mock_gui
    assert co.session == mock_session
    assert co.api_threads == {}


def test_Controller_setup(homedir, config, mocker):
    """
    Ensure the application is set up with the following default state:
    Using the `config` fixture to ensure the config is written to disk.
    """
    co = Controller('http://localhost', mocker.MagicMock(), mocker.MagicMock(), homedir)
    co.update_sources = mocker.MagicMock()

    co.setup()

    co.gui.setup.assert_called_once_with(co)


def test_Controller_start_message_thread(homedir, config, mocker):
    """
    When starting message-fetching thread, make sure we do a few things.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    mock_qthread = mocker.patch('securedrop_client.logic.QThread')
    mocker.patch('securedrop_client.logic.MessageSync')
    co.message_sync = mocker.MagicMock()
    co.start_message_thread()
    co.message_sync.moveToThread.assert_called_once_with(mock_qthread())
    co.message_thread.started.connect.assert_called_once_with(co.message_sync.run)
    co.message_thread.start.assert_called_once_with()


def test_Controller_start_message_thread_if_already_running(homedir, config, mocker):
    """
    Ensure that when starting the message thread, we don't start another thread
    if it's already running. Instead, we just authenticate the existing thread.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.api = 'api object'
    co.message_sync = mocker.MagicMock()
    co.message_thread = mocker.MagicMock()
    co.message_thread.api = None
    co.start_message_thread()
    co.message_sync.api = co.api
    co.message_thread.start.assert_not_called()


def test_Controller_start_reply_thread(homedir, config, mocker):
    """
    When starting reply-fetching thread, make sure we do a few things.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    mock_qthread = mocker.patch('securedrop_client.logic.QThread')
    mocker.patch('securedrop_client.logic.ReplySync')
    co.reply_sync = mocker.MagicMock()
    co.start_reply_thread()
    co.reply_sync.moveToThread.assert_called_once_with(mock_qthread())
    co.reply_thread.started.connect.assert_called_once_with(
        co.reply_sync.run)
    co.reply_thread.start.assert_called_once_with()


def test_Controller_start_reply_thread_if_already_running(homedir, config, mocker):
    """
    Ensure that when starting the reply thread, we don't start another thread
    if it's already running. Instead, we just authenticate the existing thread.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.api = 'api object'
    co.reply_sync = mocker.MagicMock()
    co.reply_thread = mocker.MagicMock()
    co.reply_thread.api = None
    co.start_reply_thread()
    co.reply_sync.api = co.api
    co.reply_thread.start.assert_not_called()


def test_Controller_call_api(homedir, config, mocker):
    """
    A new thread and APICallRunner is created / setup.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.finish_api_call = mocker.MagicMock()
    mocker.patch('securedrop_client.logic.QThread')
    mocker.patch('securedrop_client.logic.APICallRunner')
    mocker.patch('securedrop_client.logic.QTimer')
    mock_api_call = mocker.MagicMock()
    mock_success_callback = mocker.MagicMock()
    mock_failure_callback = mocker.MagicMock()

    co.call_api(mock_api_call, mock_success_callback, mock_failure_callback, 'foo', bar='baz')

    assert len(co.api_threads) == 1
    thread_info = co.api_threads[list(co.api_threads.keys())[0]]
    thread = thread_info['thread']
    runner = thread_info['runner']
    thread.started.connect.assert_called_once_with(runner.call_api)
    thread.start.assert_called_once_with()
    runner.moveToThread.assert_called_once_with(thread)
    runner.call_succeeded.connect.call_count == 1
    runner.call_failed.connect.call_count == 1
    runner.call_timed_out.connect.call_count == 1


def test_Controller_login(homedir, config, mocker):
    """
    Ensures the API is called in the expected manner for logging in the user
    given the username, password and 2fa token.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.call_api = mocker.MagicMock()
    mock_api = mocker.patch('securedrop_client.logic.sdclientapi.API')
    co.login('username', 'password', '123456')
    co.call_api.assert_called_once_with(mock_api().authenticate,
                                        co.on_authenticate_success,
                                        co.on_authenticate_failure)


def test_Controller_login_offline_mode(homedir, config, mocker):
    """
    Ensures user is not authenticated when logging in in offline mode and that the correct windows
    are displayed.
    """
    co = Controller('http://localhost', mocker.MagicMock(), mocker.MagicMock(), homedir)
    co.call_api = mocker.MagicMock()
    co.gui = mocker.MagicMock()
    co.gui.show_main_window = mocker.MagicMock()
    co.gui.hide_login = mocker.MagicMock()
    co.start_message_thread = mocker.MagicMock()
    co.start_reply_thread = mocker.MagicMock()
    co.update_sources = mocker.MagicMock()

    co.login_offline_mode()

    assert co.call_api.called is False
    assert co.is_authenticated is False
    co.gui.show_main_window.assert_called_once_with()
    co.gui.hide_login.assert_called_once_with()
    co.start_message_thread.assert_called_once_with()
    co.update_sources.assert_called_once_with()


def test_Controller_on_authenticate_failure(homedir, config, mocker):
    """
    If the server responds with a negative to the request to authenticate, make
    sure the user knows.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    result_data = Exception('oh no')
    co.on_authenticate_failure(result_data)
    mock_gui.show_login_error.\
        assert_called_once_with(error='There was a problem signing in. Please '
                                'verify your credentials and try again.')


def test_Controller_on_authenticate_success(homedir, config, mocker):
    """
    Ensure the client syncs when the user successfully logs in.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.sync_api = mocker.MagicMock()
    co.api = mocker.MagicMock()
    co.start_message_thread = mocker.MagicMock()
    co.start_reply_thread = mocker.MagicMock()
    co.api.username = 'test'

    co.on_authenticate_success(True)

    co.sync_api.assert_called_once_with()
    co.start_message_thread.assert_called_once_with()
    co.gui.show_main_window.assert_called_once_with('test')
    co.gui.clear_error_status.assert_called_once_with()


def test_Controller_completed_api_call_without_current_object(homedir, config, mocker):
    """
    Ensure that cleanup is performed if an API call returns in the expected
    time.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    mock_thread = mocker.MagicMock()
    mock_runner = mocker.MagicMock()
    mock_runner.result = 'result'
    mock_runner.current_object = None
    co.api_threads = {
        'thread_uuid': {
            'thread': mock_thread,
            'runner': mock_runner,
        }
    }
    mock_user_callback = mocker.MagicMock()
    co.completed_api_call('thread_uuid', mock_user_callback)
    mock_user_callback.assert_called_once_with('result')


def test_Controller_completed_api_call_with_current_object(homedir, config, mocker):
    """
    Ensure that cleanup is performed if an API call returns in the expected
    time.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    mock_thread = mocker.MagicMock()
    mock_runner = mocker.MagicMock()
    mock_runner.result = 'result'
    mock_runner.current_object = 'current_object'
    co.api_threads = {
        'thread_uuid': {
            'thread': mock_thread,
            'runner': mock_runner,
        }
    }
    mock_user_callback = mocker.MagicMock()

    mock_arg_spec = mocker.MagicMock(args=['foo', 'current_object'])
    mocker.patch('securedrop_client.logic.inspect.getfullargspec', return_value=mock_arg_spec)

    co.completed_api_call('thread_uuid', mock_user_callback)
    mock_user_callback.assert_called_once_with('result',
                                               current_object='current_object')


def test_Controller_on_action_requiring_login(homedir, config, mocker):
    """
    Ensure that when on_action_requiring_login is called, an error
    is shown in the GUI status area.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.on_action_requiring_login()
    mock_gui.update_error_status.assert_called_once_with(
        'You must sign in to perform this action.')


def test_Controller_authenticated_yes(homedir, config, mocker):
    """
    If the API is authenticated return True.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.api = mocker.MagicMock()
    co.api.token = 'foo'
    assert co.authenticated() is True


def test_Controller_authenticated_no(homedir, config, mocker):
    """
    If the API is authenticated return True.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.api = mocker.MagicMock()
    co.api.token = None
    assert co.authenticated() is False


def test_Controller_authenticated_no_api(homedir, config, mocker):
    """
    If the API is authenticated return True.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.api = None
    assert co.authenticated() is False


def test_Controller_sync_api_not_authenticated(homedir, config, mocker):
    """
    If the API isn't authenticated, don't sync.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.authenticated = mocker.MagicMock(return_value=False)
    co.call_api = mocker.MagicMock()
    co.sync_api()
    assert co.call_api.call_count == 0


def test_Controller_sync_api(homedir, config, mocker):
    """
    Sync the API is authenticated.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.authenticated = mocker.MagicMock(return_value=True)
    co.call_api = mocker.MagicMock()
    co.sync_api()
    co.call_api.assert_called_once_with(storage.get_remote_data,
                                        co.on_sync_success,
                                        co.on_sync_failure,
                                        co.api)


def test_Controller_last_sync_with_file(homedir, config, mocker):
    """
    The flag indicating the time of the last sync with the API is stored in a
    dotfile in the user's home directory. If such a file exists, ensure an
    "arrow" object (representing the date/time) is returned.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    timestamp = '2018-10-10 18:17:13+01:00'
    mocker.patch("builtins.open", mocker.mock_open(read_data=timestamp))
    result = co.last_sync()
    assert isinstance(result, arrow.Arrow)
    assert result.format() == timestamp


def test_Controller_last_sync_no_file(homedir, config, mocker):
    """
    If there's no sync file, then just return None.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    mocker.patch("builtins.open", mocker.MagicMock(side_effect=Exception()))
    assert co.last_sync() is None


def test_Controller_on_sync_failure(homedir, config, mocker):
    """
    If there's no result to syncing, then don't attempt to update local storage
    and perhaps implement some as-yet-undefined UI update.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.update_sources = mocker.MagicMock()
    result_data = Exception('Boom')  # Not the expected tuple.
    mock_storage = mocker.patch('securedrop_client.logic.storage')
    co.on_sync_failure(result_data)
    assert mock_storage.update_local_storage.call_count == 0
    co.update_sources.assert_called_once_with()


def test_Controller_on_sync_success(homedir, config, mocker):
    """
    If there's a result to syncing, then update local storage.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.update_sources = mocker.MagicMock()
    co.api_runner = mocker.MagicMock()
    co.gpg = mocker.MagicMock()

    result_data = ('sources', 'submissions', 'replies')

    co.update_sources = mocker.MagicMock()
    co.api_runner = mocker.MagicMock()

    mock_source = mocker.MagicMock()
    mock_source.key = {
        'type': 'PGP',
        'public': PUB_KEY,
    }

    mock_sources = [mock_source]

    result_data = (mock_sources, 'submissions', 'replies')

    co.call_reset = mocker.MagicMock()
    mock_storage = mocker.patch('securedrop_client.logic.storage')
    co.on_sync_success(result_data)
    mock_storage.update_local_storage. \
        assert_called_once_with(mock_session, mock_sources, "submissions",
                                "replies",
                                os.path.join(homedir, 'data'))

    co.update_sources.assert_called_once_with()


def test_Controller_on_sync_success_with_non_pgp_key(homedir, config, mocker):
    """
    If there's a result to syncing, then update local storage.
    This is it to check that we can gracefully handle missing keys.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.update_sources = mocker.MagicMock()
    co.api_runner = mocker.MagicMock()

    mock_source = mocker.MagicMock()
    mock_source.key = {
        'type': 'PGP',
    }

    mock_sources = [mock_source]
    result_data = (mock_sources, 'submissions', 'replies')

    co.call_reset = mocker.MagicMock()
    mock_storage = mocker.patch('securedrop_client.logic.storage')
    co.on_sync_success(result_data)
    mock_storage.update_local_storage. \
        assert_called_once_with(mock_session, mock_sources, "submissions",
                                "replies",
                                os.path.join(homedir, 'data'))
    co.update_sources.assert_called_once_with()


def test_Controller_on_sync_success_with_key_import_fail(homedir, config, mocker):
    """
    If there's a result to syncing, then update local storage.
    This is it to check that we can gracefully handle an import failure.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.update_sources = mocker.MagicMock()
    co.api_runner = mocker.MagicMock()

    mock_source = mocker.MagicMock()
    mock_source.key = {
        'type': 'PGP',
        'public': PUB_KEY,
    }

    mock_sources = [mock_source]
    result_data = (mock_sources, 'submissions', 'replies')

    co.call_reset = mocker.MagicMock()
    mock_storage = mocker.patch('securedrop_client.logic.storage')
    mocker.patch.object(co.gpg, 'import_key', side_effect=CryptoError)
    co.on_sync_success(result_data)
    mock_storage.update_local_storage. \
        assert_called_once_with(mock_session, mock_sources, "submissions",
                                "replies",
                                os.path.join(homedir, 'data'))
    co.update_sources.assert_called_once_with()


def test_Controller_update_sync(homedir, config, mocker):
    """
    Cause the UI to update with the result of self.last_sync().
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.last_sync = mocker.MagicMock()
    co.update_sync()
    assert co.last_sync.call_count == 1
    co.gui.show_sync.assert_called_once_with(co.last_sync())


def test_Controller_update_sources(homedir, config, mocker):
    """
    Ensure the UI displays a list of the available sources from local data
    store.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    mock_storage = mocker.patch('securedrop_client.logic.storage')
    source_list = [factory.Source(last_updated=2), factory.Source(last_updated=1)]
    mock_storage.get_local_sources.return_value = source_list
    co.update_sources()
    mock_storage.get_local_sources.assert_called_once_with(mock_session)
    mock_gui.show_sources.assert_called_once_with(source_list)


def test_Controller_unstars_a_source_if_starred(homedir, config, mocker):
    """
    Ensure that the client unstars a source if it is starred.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)

    source_db_object = mocker.MagicMock()
    source_db_object.uuid = mocker.MagicMock()
    source_db_object.is_starred = True

    co.call_api = mocker.MagicMock()
    co.api = mocker.MagicMock()
    co.api.remove_star = mocker.MagicMock()
    co.on_update_star_success = mocker.MagicMock()
    co.on_update_star_failure = mocker.MagicMock()

    source_sdk_object = mocker.MagicMock()
    mock_source = mocker.patch('sdclientapi.Source')
    mock_source.return_value = source_sdk_object
    co.update_star(source_db_object)

    co.call_api.assert_called_once_with(
        co.api.remove_star,
        co.on_update_star_success,
        co.on_update_star_failure,
        source_sdk_object,
    )
    mock_gui.clear_error_status.assert_called_once_with()


def test_Controller_unstars_a_source_if_unstarred(homedir, config, mocker):
    """
    Ensure that the client stars a source if it is unstarred.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)

    source_db_object = mocker.MagicMock()
    source_db_object.uuid = mocker.MagicMock()
    source_db_object.is_starred = False

    co.call_api = mocker.MagicMock()
    co.api = mocker.MagicMock()
    co.api.add_star = mocker.MagicMock()
    co.on_update_star_success = mocker.MagicMock()
    co.on_update_star_failure = mocker.MagicMock()

    source_sdk_object = mocker.MagicMock()
    mock_source = mocker.patch('sdclientapi.Source')
    mock_source.return_value = source_sdk_object
    co.update_star(source_db_object)

    co.call_api.assert_called_once_with(
        co.api.add_star,
        co.on_update_star_success,
        co.on_update_star_failure,
        source_sdk_object,
    )
    mock_gui.clear_error_status.assert_called_once_with()


def test_Controller_update_star_not_logged_in(homedir, config, mocker):
    """
    Ensure that starring/unstarring a source when not logged in calls
    the method that displays an error status in the left sidebar.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    source_db_object = mocker.MagicMock()
    co.on_action_requiring_login = mocker.MagicMock()
    co.api = None
    co.update_star(source_db_object)
    co.on_action_requiring_login.assert_called_with()


def test_Controller_on_update_star_success(homedir, config, mocker):
    """
    If the starring occurs successfully, then a sync should occur to update
    locally.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    result = True
    co.call_reset = mocker.MagicMock()
    co.sync_api = mocker.MagicMock()
    co.on_update_star_success(result)
    co.sync_api.assert_called_once_with()
    mock_gui.clear_error_status.assert_called_once_with()


def test_Controller_on_update_star_failed(homedir, config, mocker):
    """
    If the starring does not occur properly, then an error should appear
    on the error status sidebar, and a sync will not occur.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    result = Exception('boom')
    co.call_reset = mocker.MagicMock()
    co.sync_api = mocker.MagicMock()
    co.on_update_star_failure(result)
    co.sync_api.assert_not_called()
    mock_gui.update_error_status.assert_called_once_with('Failed to update star.')


def test_Controller_logout(homedir, config, mocker):
    """
    The API is reset to None and the UI is set to logged out state.
    The message and reply threads should also have the
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.api = mocker.MagicMock()
    co.message_sync = mocker.MagicMock()
    co.reply_sync = mocker.MagicMock()
    co.message_sync.api = mocker.MagicMock()
    co.reply_sync.api = mocker.MagicMock()
    co.logout()
    assert co.api is None
    assert co.message_sync.api is None
    assert co.reply_sync.api is None
    co.gui.logout.assert_called_once_with()


def test_Controller_set_activity_status(homedir, config, mocker):
    """
    Ensure the GUI set_status API is called.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.set_status("Hello, World!", 1000)
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
            Controller('http://localhost', mock_gui, mock_session, sdc_home)

        if case['should_pass']:
            func()
        else:
            with pytest.raises(RuntimeError):
                func()

    # check that both mocks were called to ensure they aren't "dead code"
    assert mock_open.called
    assert mock_json.called


def test_Controller_on_file_download_Submission(homedir, config, mocker):
    """
    If the handler is passed a submission, check the download_submission
    function is the one called against the API.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.call_api = mocker.MagicMock()
    co.api = mocker.MagicMock()

    source = factory.Source()
    file_ = db.File(source=source, uuid='uuid', size=1234, filename='1-myfile.doc.gpg',
                    download_url='http://myserver/myfile', is_downloaded=False)

    submission_sdk_object = mocker.MagicMock()
    mock_submission = mocker.patch('sdclientapi.Submission')
    mock_submission.return_value = submission_sdk_object

    co.on_file_download(source, file_)
    co.call_api.assert_called_once_with(
        co.api.download_submission,
        co.on_file_download_success,
        co.on_file_download_failure,
        submission_sdk_object,
        co.data_dir,
        current_object=file_,
    )


def test_Controller_on_file_downloaded_success(homedir, config, mocker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.update_sources = mocker.MagicMock()
    co.api_runner = mocker.MagicMock()
    co.file_ready = mocker.MagicMock()  # signal when file is downloaded

    test_filename = "1-my-file-location-msg.gpg"
    test_object_uuid = 'uuid-of-downloaded-object'
    co.call_reset = mocker.MagicMock()
    result_data = ('this-is-a-sha256-sum', test_filename)
    submission_db_object = mocker.MagicMock()
    submission_db_object.uuid = test_object_uuid
    submission_db_object.filename = test_filename
    mock_storage = mocker.patch('securedrop_client.logic.storage')
    mock_gpg = mocker.patch.object(co.gpg, 'decrypt_submission_or_reply', return_value='filepath')
    mocker.patch('shutil.move')

    co.on_file_download_success(result_data, current_object=submission_db_object)

    mock_gpg.call_count == 1
    mock_storage.mark_file_as_downloaded.assert_called_once_with(
        test_object_uuid, mock_session)
    mock_storage.set_object_decryption_status_with_content.assert_called_once_with(
        submission_db_object, mock_session, True)

    # Signal should be emitted with UUID of the successfully downloaded object
    co.file_ready.emit.assert_called_once_with(test_object_uuid)


def test_Controller_on_file_downloaded_api_failure(homedir, config, mocker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.file_ready = mocker.MagicMock()  # signal when file is downloaded
    co.update_sources = mocker.MagicMock()
    co.api_runner = mocker.MagicMock()

    test_filename = "1-my-file-location-msg.gpg"
    co.api_runner.result = ("", test_filename)
    co.call_reset = mocker.MagicMock()
    co.set_status = mocker.MagicMock()
    result_data = Exception('error message')
    submission_db_object = mocker.MagicMock()
    submission_db_object.uuid = 'myuuid'
    submission_db_object.filename = 'filename'

    co.on_file_download_failure(result_data, current_object=submission_db_object)

    co.set_status.assert_called_once_with("The file download failed. Please try again.")
    co.file_ready.emit.assert_not_called()


def test_Controller_on_file_downloaded_decrypt_failure(homedir, config, mocker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)

    co.update_sources = mocker.MagicMock()
    co.api_runner = mocker.MagicMock()
    co.file_ready = mocker.MagicMock()  # signal when file is downloaded

    test_filename = "1-my-file-location-msg.gpg"
    co.api_runner.result = ("", test_filename)
    co.set_status = mocker.MagicMock()

    result_data = ('this-is-a-sha256-sum', test_filename)
    submission_db_object = mocker.MagicMock()
    submission_db_object.uuid = 'myuuid'
    submission_db_object.filename = 'filename'
    mock_gpg = mocker.patch.object(co.gpg, 'decrypt_submission_or_reply',
                                   side_effect=CryptoError())
    mock_storage = mocker.patch('securedrop_client.logic.storage')
    mocker.patch('shutil.move')

    co.on_file_download_success(result_data, current_object=submission_db_object)
    mock_gpg.call_count == 1
    co.set_status.assert_called_once_with(
        "Failed to decrypt file, please try again or talk to your administrator.")
    mock_storage.set_object_decryption_status_with_content.assert_called_once_with(
        submission_db_object, mock_session, False)
    co.file_ready.emit.assert_not_called()


def test_Controller_on_file_download_user_not_signed_in(homedir, config, mocker):
    """
    If a user clicks the download button but is not logged in,
    an error should appear.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    source = factory.Source()
    file_ = db.File(source=source, uuid='uuid', size=1234, filename='1-myfile.doc.gpg',
                    download_url='http://myserver/myfile', is_downloaded=False)
    co.on_action_requiring_login = mocker.MagicMock()
    co.api = None
    submission_sdk_object = mocker.MagicMock()
    mock_submission = mocker.patch('sdclientapi.Submission')
    mock_submission.return_value = submission_sdk_object
    co.on_file_download(source, file_)
    co.on_action_requiring_login.assert_called_once_with()


def test_Controller_on_file_download_Reply(homedir, config, mocker):
    """
    If the handler is passed a reply, check the download_reply
    function is the one called against the API.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    source = factory.Source()
    journalist = db.User('Testy mcTestface')
    reply = db.Reply(uuid='reply-uuid',
                     journalist=journalist,
                     source=source,
                     filename='1-my-reply.gpg',
                     size=123)  # Not a sdclientapi.Submission
    co.call_api = mocker.MagicMock()
    co.api = mocker.MagicMock()
    reply_sdk_object = mocker.MagicMock()
    mock_reply = mocker.patch('sdclientapi.Reply')
    mock_reply.return_value = reply_sdk_object
    co.on_file_download(source, reply)
    co.call_api.assert_called_once_with(co.api.download_reply,
                                        co.on_file_download_success,
                                        co.on_file_download_failure,
                                        reply_sdk_object,
                                        co.data_dir,
                                        current_object=reply)


def test_Controller_on_file_open(homedir, config, mocker):
    """
    If running on Qubes, a new QProcess with the expected command and args
    should be started.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.proxy = True
    mock_submission = mocker.MagicMock()
    mock_submission.filename = '1-test.pdf'
    mock_subprocess = mocker.MagicMock()
    mock_process = mocker.MagicMock(return_value=mock_subprocess)
    mocker.patch('securedrop_client.logic.QProcess', mock_process)
    co.on_file_open(mock_submission)
    mock_process.assert_called_once_with(co)
    mock_subprocess.start.call_count == 1


def test_Controller_on_delete_source_success(homedir, config, mocker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.sync_api = mocker.MagicMock()
    co.on_delete_source_success(True)
    co.sync_api.assert_called_with()
    co.gui.clear_error_status.assert_called_with()


def test_Controller_on_delete_source_failure(homedir, config, mocker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.sync_api = mocker.MagicMock()
    co.on_delete_source_failure(Exception())
    co.gui.update_error_status.assert_called_with('Failed to delete source at server')


def test_Controller_delete_source(homedir, config, mocker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.call_api = mocker.MagicMock()
    co.api = mocker.MagicMock()
    co.delete_source(mock_source)
    co.call_api.assert_called_with(
        co.api.delete_source,
        co.on_delete_source_success,
        co.on_delete_source_failure,
        mock_source
    )


def test_Controller_send_reply_success(homedir, mocker):
    '''
    Check that the "happy path" of encrypting a message and sending it to the sever behaves as
    expected.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    co = Controller('http://localhost', mock_gui, mock_session, homedir)

    co.call_api = mocker.Mock()
    co.api = mocker.Mock()
    encrypted_reply = 's3kr1t m3ss1dg3'
    mock_encrypt = mocker.patch.object(co.gpg, 'encrypt_to_source', return_value=encrypted_reply)
    source_uuid = 'abc123'
    msg_uuid = 'xyz456'
    msg = 'wat'
    mock_sdk_source = mocker.Mock()
    mock_source_init = mocker.patch('securedrop_client.logic.sdclientapi.Source',
                                    return_value=mock_sdk_source)

    co.send_reply(source_uuid, msg_uuid, msg)

    # ensure message is encrypted
    mock_encrypt.assert_called_once_with(source_uuid, msg)

    # ensure api is called
    co.call_api.assert_called_once_with(
        co.api.reply_source,
        co.on_reply_success,
        co.on_reply_failure,
        mock_sdk_source,
        encrypted_reply,
        msg_uuid,
        current_object=(source_uuid, msg_uuid),
    )

    assert mock_source_init.called  # to prevent stale mocks


def test_Controller_send_reply_gpg_error(homedir, mocker):
    '''
    Check that if gpg fails when sending a message, we alert the UI and do *not* call the API.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    co = Controller('http://localhost', mock_gui, mock_session, homedir)

    co.call_api = mocker.Mock()
    co.api = mocker.Mock()
    mock_encrypt = mocker.patch.object(co.gpg, 'encrypt_to_source', side_effect=Exception)
    source_uuid = 'abc123'
    msg_uuid = 'xyz456'
    msg = 'wat'
    mock_sdk_source = mocker.Mock()
    mock_source_init = mocker.patch('securedrop_client.logic.sdclientapi.Source',
                                    return_value=mock_sdk_source)
    mock_reply_failed = mocker.patch.object(co, 'reply_failed')

    co.send_reply(source_uuid, msg_uuid, msg)

    # ensure there is an attempt to encrypt the message
    mock_encrypt.assert_called_once_with(source_uuid, msg)

    # ensure we emit a failure on gpg errors
    mock_reply_failed.emit.assert_called_once_with(msg_uuid)

    # ensure api not is called after a gpg error
    assert not co.call_api.called

    assert mock_source_init.called  # to prevent stale mocks


def test_Controller_on_reply_success(homedir, mocker):
    '''
    Check that when the result is a success, the client emits the correct signal.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_reply_init = mocker.patch('securedrop_client.logic.db.Reply')

    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.api = mocker.Mock()
    journalist_uuid = 'abc123'
    co.api.token_journalist_uuid = journalist_uuid
    mock_reply_succeeded = mocker.patch.object(co, 'reply_succeeded')
    mock_reply_failed = mocker.patch.object(co, 'reply_failed')

    reply = sdlocalobjects.Reply(uuid='xyz456', filename='1-wat.gpg')

    source_uuid = 'foo111'
    msg_uuid = 'bar222'
    current_object = (source_uuid, msg_uuid)
    co.on_reply_success(reply, current_object)
    co.session.commit.assert_called_once_with()
    mock_reply_succeeded.emit.assert_called_once_with(msg_uuid)
    assert not mock_reply_failed.emit.called

    assert mock_reply_init.called  # to prevent stale mocks


def test_Controller_on_reply_failure(homedir, mocker):
    '''
    Check that when the result is a failure, the client emits the correct signal.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.api = mocker.Mock()
    journalist_uuid = 'abc123'
    co.api.token_journalist_uuid = journalist_uuid
    mock_reply_succeeded = mocker.patch.object(co, 'reply_succeeded')
    mock_reply_failed = mocker.patch.object(co, 'reply_failed')

    source_uuid = 'foo111'
    msg_uuid = 'bar222'
    current_object = (source_uuid, msg_uuid)
    co.on_reply_failure(Exception, current_object)
    mock_reply_failed.emit.assert_called_once_with(msg_uuid)
    assert not mock_reply_succeeded.emit.called


def test_Controller_is_authenticated_property(homedir, mocker):
    '''
    Check that the @property `is_authenticated`:
      - Cannot be deleted
      - Emits the correct signals when updated
      - Sets internal state to ensure signals are only set when the state changes
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    mock_signal = mocker.patch.object(co, 'authentication_state')

    # default state is unauthenticated
    assert co.is_authenticated is False

    # the property cannot be deleted
    with pytest.raises(AttributeError):
        del co.is_authenticated

    # setting the signal to its current value does not fire the signal
    co.is_authenticated = False
    assert not mock_signal.emit.called
    assert co.is_authenticated is False

    # setting the property to True sends a signal
    co.is_authenticated = True
    mock_signal.emit.assert_called_once_with(True)
    assert co.is_authenticated is True

    mock_signal.reset_mock()

    co.is_authenticated = False
    mock_signal.emit.assert_called_once_with(False)
    assert co.is_authenticated is False


def test_APICallRunner_api_call_timeout(mocker):
    """
    Ensure that if a RequestTimeoutError is raised, both the failure and timeout signals are
    emitted.
    """
    mock_api = mocker.MagicMock()
    mock_api.fake_request = mocker.MagicMock(side_effect=RequestTimeoutError())

    runner = APICallRunner(mock_api.fake_request)

    mock_failure_signal = mocker.patch.object(runner, 'call_failed')
    mock_timeout_signal = mocker.patch.object(runner, 'call_timed_out')

    runner.call_api()

    mock_api.fake_request.assert_called_once_with()
    mock_failure_signal.emit.assert_called_once_with()
    mock_timeout_signal.emit.assert_called_once_with()


def test_Controller_api_call_timeout(homedir, config, mocker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, mock_session, homedir)
    co.on_api_timeout()
    mock_gui.update_error_status.assert_called_once_with(
        'The connection to the SecureDrop server timed out. Please try again.')
