"""
Make sure the Client object, containing the application logic, behaves as
expected.
"""
import arrow
from datetime import datetime
import os
import pytest
import sdclientapi
import shutil
from securedrop_client import storage, models
from securedrop_client.logic import APICallRunner, Client
from unittest import mock


def test_APICallRunner_init():
    """
    Ensure everything is set up as expected.
    """
    mock_api_call = mock.MagicMock()
    mock_current_object = mock.MagicMock()
    cr = APICallRunner(mock_api_call, mock_current_object, 'foo', bar='baz')
    assert cr.api_call == mock_api_call
    assert cr.current_object == mock_current_object
    assert cr.args == ('foo', )
    assert cr.kwargs == {'bar': 'baz', }


def test_APICallRunner_call_api():
    """
    A result is obtained so emit True and put the result in self.result.
    """
    mock_api_call = mock.MagicMock(return_value='foo')
    mock_api_call.__name__ = 'my_function'
    mock_current_object = mock.MagicMock()
    cr = APICallRunner(mock_api_call, mock_current_object, 'foo', bar='baz')
    cr.call_finished = mock.MagicMock()
    cr.call_api()
    assert cr.result == 'foo'
    cr.call_finished.emit.assert_called_once_with()


def test_APICallRunner_with_exception():
    """
    An exception has occured so emit False.
    """
    ex = Exception('boom')
    mock_api_call = mock.MagicMock(side_effect=ex)
    mock_api_call.__name__ = 'my_function'
    mock_current_object = mock.MagicMock()
    cr = APICallRunner(mock_api_call, mock_current_object, 'foo', bar='baz')
    cr.call_finished = mock.MagicMock()
    with mock.patch('securedrop_client.logic.QTimer') as mock_timer:
        cr.call_api()
    assert cr.result == ex
    cr.call_finished.emit.assert_called_once_with()


def test_Client_init(safe_tmpdir):
    """
    The passed in gui, app and session instances are correctly referenced and,
    where appropriate, have a reference back to the client.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost/', mock_gui, mock_session, str(safe_tmpdir))
    assert cl.hostname == 'http://localhost/'
    assert cl.gui == mock_gui
    assert cl.session == mock_session
    assert cl.api_threads == {}


def test_Client_setup(safe_tmpdir):
    """
    Ensure the application is set up with the following default state:
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.update_sources = mock.MagicMock()
    cl.setup()
    cl.gui.setup.assert_called_once_with(cl)
    cl.update_sources.assert_called_once_with()
    cl.gui.show_login.assert_called_once_with()

def test_Client_start_message_thread(safe_tmpdir):
    """
    When starting message-fetching thread, make sure we do a few things.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    with mock.patch('securedrop_client.logic.QThread') as mock_qthread, \
         mock.patch('securedrop_client.logic.MessageSync') as mock_msync:
        cl.message_sync = mock.MagicMock()
        cl.start_message_thread()
        cl.message_sync.moveToThread.assert_called_once_with(mock_qthread())
        cl.message_thread.started.connect.assert_called_once_with(cl.message_sync.run)
        cl.message_thread.start.assert_called_once_with()


def test_Client_call_api(safe_tmpdir):
    """
    A new thread and APICallRunner is created / setup.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.finish_api_call = mock.MagicMock()
    with mock.patch('securedrop_client.logic.QThread') as mock_qthread, \
            mock.patch(
                'securedrop_client.logic.APICallRunner') as mock_runner, \
            mock.patch('securedrop_client.logic.QTimer') as mock_timer:
        mock_api_call = mock.MagicMock()
        mock_callback = mock.MagicMock()
        mock_timeout = mock.MagicMock()
        cl.call_api(mock_api_call, mock_callback, mock_timeout, 'foo',
                    bar='baz')
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


def test_Client_clean_thread_no_thread(safe_tmpdir):
    """
    The client will ignore an attempt to reset an API call if there's no such
    call "in flight".
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.finish_api_call = mock.MagicMock()
    cl.api_threads = {'a': 'b'}
    cl.clean_thread('foo')
    assert len(cl.api_threads) == 1


def test_Client_clean_thread(safe_tmpdir):
    """
    Cleaning up an existing thread disconnects the timer and removes it from
    the api_threads collection.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    mock_timer = mock.MagicMock()
    cl.api_threads = {
        'foo': {
            'timer': mock_timer,
        }
    }
    cl.clean_thread('foo')
    assert mock_timer.disconnect.call_count == 1
    assert 'foo' not in cl.api_threads


def test_Client_login(safe_tmpdir):
    """
    Ensures the API is called in the expected manner for logging in the user
    given the username, password and 2fa token.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.call_api = mock.MagicMock()
    with mock.patch('securedrop_client.logic.sdclientapi.API') as mock_api:
        cl.login('username', 'password', '123456')
        cl.call_api.assert_called_once_with(mock_api().authenticate,
                                            cl.on_authenticate,
                                            cl.on_login_timeout)


def test_Client_on_authenticate_failed(safe_tmpdir):
    """
    If the server responds with a negative to the request to authenticate, make
    sure the user knows.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    result_data = 'false'
    cl.on_authenticate(result_data)
    mock_gui.show_login_error.\
        assert_called_once_with(error='There was a problem signing in. Please '
                                'verify your credentials and try again.')


def test_Client_on_authenticate_ok(safe_tmpdir):
    """
    Ensure the client syncs when the user successfully logs in.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.sync_api = mock.MagicMock()
    cl.api = mock.MagicMock()
    cl.start_message_thread = mock.MagicMock()
    cl.api.username = 'test'
    cl.on_authenticate(True)
    cl.sync_api.assert_called_once_with()
    cl.start_message_thread.assert_called_once_with()
    cl.gui.set_logged_in_as.assert_called_once_with('test')
    # Error status bar should be cleared
    cl.gui.update_error_status.assert_called_once_with("")


def test_Client_completed_api_call_without_current_object(safe_tmpdir):
    """
    Ensure that cleanup is performed if an API call returns in the expected
    time.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    mock_thread = mock.MagicMock()
    mock_runner = mock.MagicMock()
    mock_runner.result = 'result'
    mock_runner.current_object = None
    mock_timer = mock.MagicMock()
    cl.api_threads = {
        'thread_uuid': {
            'thread': mock_thread,
            'runner': mock_runner,
            'timer': mock_timer,
        }
    }
    cl.clean_thread = mock.MagicMock()
    mock_user_callback = mock.MagicMock()
    cl.completed_api_call('thread_uuid', mock_user_callback)
    cl.clean_thread.assert_called_once_with('thread_uuid')
    mock_user_callback.assert_called_once_with('result')
    mock_timer.stop.assert_called_once_with()


def test_Client_completed_api_call_with_current_object(safe_tmpdir):
    """
    Ensure that cleanup is performed if an API call returns in the expected
    time.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    mock_thread = mock.MagicMock()
    mock_runner = mock.MagicMock()
    mock_runner.result = 'result'
    mock_runner.current_object = 'current_object'
    mock_timer = mock.MagicMock()
    cl.api_threads = {
        'thread_uuid': {
            'thread': mock_thread,
            'runner': mock_runner,
            'timer': mock_timer,
        }
    }
    cl.clean_thread = mock.MagicMock()
    mock_user_callback = mock.MagicMock()
    cl.completed_api_call('thread_uuid', mock_user_callback)
    cl.clean_thread.assert_called_once_with('thread_uuid')
    mock_user_callback.assert_called_once_with('result',
                                               current_object='current_object')
    mock_timer.stop.assert_called_once_with()


def test_Client_timeout_cleanup_without_current_object(safe_tmpdir):
    """
    Ensure that cleanup is performed if an API call times out.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    mock_thread = mock.MagicMock()
    mock_runner = mock.MagicMock()
    mock_runner.current_object = None
    mock_timer = mock.MagicMock()
    cl.api_threads = {
        'thread_uuid': {
            'thread': mock_thread,
            'runner': mock_runner,
            'timer': mock_timer,
        }
    }
    cl.clean_thread = mock.MagicMock()
    mock_user_callback = mock.MagicMock()
    cl.timeout_cleanup('thread_uuid', mock_user_callback)
    assert mock_runner.i_timed_out is True
    cl.clean_thread.assert_called_once_with('thread_uuid')
    mock_user_callback.assert_called_once_with()


def test_Client_timeout_cleanup_with_current_object(safe_tmpdir):
    """
    Ensure that cleanup is performed if an API call times out.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    mock_thread = mock.MagicMock()
    mock_runner = mock.MagicMock()
    mock_runner.current_object = 'current_object'
    mock_timer = mock.MagicMock()
    cl.api_threads = {
        'thread_uuid': {
            'thread': mock_thread,
            'runner': mock_runner,
            'timer': mock_timer,
        }
    }
    cl.clean_thread = mock.MagicMock()
    mock_user_callback = mock.MagicMock()
    cl.timeout_cleanup('thread_uuid', mock_user_callback)
    assert mock_runner.i_timed_out is True
    cl.clean_thread.assert_called_once_with('thread_uuid')
    mock_user_callback.assert_called_once_with(current_object='current_object')


def test_Client_on_sync_timeout(safe_tmpdir):
    """
    Display error message in status bar if sync times out.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.api = "this is populated"
    cl.on_sync_timeout()
    assert cl.api is not None
    mock_gui.update_error_status.\
        assert_called_once_with(error='The connection to the SecureDrop '
                                'server timed out. Please try again.')


def test_Client_on_login_timeout(safe_tmpdir):
    """
    Reset the form if the API call times out.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.call_reset = mock.MagicMock()
    cl.on_login_timeout()
    assert cl.api is None
    mock_gui.show_login_error.\
        assert_called_once_with(error='The connection to the SecureDrop '
                                'server timed out. Please try again.')


def test_Client_on_action_requiring_login(safe_tmpdir):
    """
    Ensure that when on_action_requiring_login is called, an error
    is shown in the GUI status area.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.on_action_requiring_login()
    mock_gui.update_error_status.assert_called_once_with(
        'You must sign in to perform this action.')


def test_Client_authenticated_yes(safe_tmpdir):
    """
    If the API is authenticated return True.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.api = mock.MagicMock()
    cl.api.token = {'token': 'foo'}
    assert cl.authenticated() is True


def test_Client_authenticated_no(safe_tmpdir):
    """
    If the API is authenticated return True.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.api = mock.MagicMock()
    cl.api.token = {'token': ''}
    assert cl.authenticated() is False


def test_Client_authenticated_no_api(safe_tmpdir):
    """
    If the API is authenticated return True.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.api = None
    assert cl.authenticated() is False


def test_Client_sync_api_not_authenticated(safe_tmpdir):
    """
    If the API isn't authenticated, don't sync.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.authenticated = mock.MagicMock(return_value=False)
    cl.call_api = mock.MagicMock()
    cl.sync_api()
    assert cl.call_api.call_count == 0


def test_Client_sync_api(safe_tmpdir):
    """
    Sync the API is authenticated.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.authenticated = mock.MagicMock(return_value=True)
    cl.call_api = mock.MagicMock()
    cl.sync_api()
    cl.call_api.assert_called_once_with(storage.get_remote_data, cl.on_synced,
                                        cl.on_sync_timeout, cl.api)


def test_Client_last_sync_with_file(safe_tmpdir):
    """
    The flag indicating the time of the last sync with the API is stored in a
    dotfile in the user's home directory. If such a file exists, ensure an
    "arror" object (representing the date/time) is returned.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    timestamp = '2018-10-10 18:17:13+01:00'
    with mock.patch("builtins.open", mock.mock_open(read_data=timestamp)):
        result = cl.last_sync()
        assert isinstance(result, arrow.Arrow)
        assert result.format() == timestamp


def test_Client_last_sync_no_file(safe_tmpdir):
    """
    If there's no sync file, then just return None.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    with mock.patch("builtins.open", mock.MagicMock(side_effect=Exception())):
        assert cl.last_sync() is None


def test_Client_on_synced_no_result(safe_tmpdir):
    """
    If there's no result to syncing, then don't attempt to update local storage
    and perhaps implement some as-yet-undefined UI update.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.update_sources = mock.MagicMock()
    result_data = Exception('Boom')  # Not the expected tuple.
    with mock.patch('securedrop_client.logic.storage') as mock_storage:
        cl.on_synced(result_data)
        assert mock_storage.update_local_storage.call_count == 0
    cl.update_sources.assert_called_once_with()


def test_Client_on_synced_with_result(safe_tmpdir):
    """
    If there's a result to syncing, then update local storage.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.update_sources = mock.MagicMock()
    cl.api_runner = mock.MagicMock()
    result_data = ('sources', 'submissions', 'replies')
    cl.call_reset = mock.MagicMock()
    with mock.patch('securedrop_client.logic.storage') as mock_storage:
        cl.on_synced(result_data)
        mock_storage.update_local_storage.\
            assert_called_once_with(mock_session, "sources", "submissions",
                                    "replies")
    cl.update_sources.assert_called_once_with()


def test_Client_update_sync(safe_tmpdir):
    """
    Cause the UI to update with the result of self.last_sync().
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.last_sync = mock.MagicMock()
    cl.update_sync()
    assert cl.last_sync.call_count == 1
    cl.gui.show_sync.assert_called_once_with(cl.last_sync())


def test_Client_update_sources(safe_tmpdir):
    """
    Ensure the UI displays a list of the available sources from local data
    store.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    with mock.patch('securedrop_client.logic.storage') as mock_storage:
        mock_storage.get_local_sources.return_value = (1, 2, 3)
        cl.update_sources()
        mock_storage.get_local_sources.assert_called_once_with(mock_session)
        mock_gui.show_sources.assert_called_once_with([1, 2, 3])


def test_Client_unstars_a_source_if_starred(safe_tmpdir):
    """
    Ensure that the client unstars a source if it is starred.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    source_db_object = mock.MagicMock()
    source_db_object.uuid = mock.MagicMock()
    source_db_object.is_starred = True
    cl.call_api = mock.MagicMock()
    cl.api = mock.MagicMock()
    cl.api.remove_star = mock.MagicMock()
    cl.on_update_star_complete = mock.MagicMock()
    cl.on_sidebar_action_timeout = mock.MagicMock()
    source_sdk_object = mock.MagicMock()
    with mock.patch('sdclientapi.Source') as mock_source:
        mock_source.return_value = source_sdk_object
        cl.update_star(source_db_object)
        cl.call_api.assert_called_once_with(
            cl.api.remove_star, cl.on_update_star_complete,
            cl.on_sidebar_action_timeout, source_sdk_object)
    mock_gui.update_error_status.assert_called_once_with("")


def test_Client_unstars_a_source_if_unstarred(safe_tmpdir):
    """
    Ensure that the client stars a source if it is unstarred.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    source_db_object = mock.MagicMock()
    source_db_object.uuid = mock.MagicMock()
    source_db_object.is_starred = False
    cl.call_api = mock.MagicMock()
    cl.api = mock.MagicMock()
    cl.api.add_star = mock.MagicMock()
    cl.on_update_star_complete = mock.MagicMock()
    cl.on_sidebar_action_timeout = mock.MagicMock()
    source_sdk_object = mock.MagicMock()
    with mock.patch('sdclientapi.Source') as mock_source:
        mock_source.return_value = source_sdk_object
        cl.update_star(source_db_object)
        cl.call_api.assert_called_once_with(
            cl.api.add_star, cl.on_update_star_complete,
            cl.on_sidebar_action_timeout, source_sdk_object)
    mock_gui.update_error_status.assert_called_once_with("")


def test_Client_update_star_not_logged_in(safe_tmpdir):
    """
    Ensure that starring/unstarring a source when not logged in calls
    the method that displays an error status in the left sidebar.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    source_db_object = mock.MagicMock()
    cl.on_action_requiring_login = mock.MagicMock()
    cl.api = None
    cl.update_star(source_db_object)
    cl.on_action_requiring_login.assert_called_with()


def test_Client_sidebar_action_timeout(safe_tmpdir):
    """
    Show on error status sidebar that a timeout occurred.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.on_sidebar_action_timeout()
    mock_gui.update_error_status.assert_called_once_with(
        'The connection to the SecureDrop server timed out. Please try again.')


def test_Client_on_update_star_success(safe_tmpdir):
    """
    If the starring occurs successfully, then a sync should occur to update
    locally.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    result = True
    cl.call_reset = mock.MagicMock()
    cl.sync_api = mock.MagicMock()
    cl.on_update_star_complete(result)
    cl.sync_api.assert_called_once_with()
    mock_gui.update_error_status.assert_called_once_with("")


def test_Client_on_update_star_failed(safe_tmpdir):
    """
    If the starring does not occur properly, then an error should appear
    on the error status sidebar, and a sync will not occur.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    result = Exception('boom')
    cl.call_reset = mock.MagicMock()
    cl.sync_api = mock.MagicMock()
    cl.on_update_star_complete(result)
    cl.sync_api.assert_not_called()
    mock_gui.update_error_status.assert_called_once_with(
        'Failed to apply change.')


def test_Client_logout(safe_tmpdir):
    """
    The API is reset to None and the UI is set to logged out state.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.api = mock.MagicMock()
    cl.logout()
    assert cl.api is None
    cl.gui.logout.assert_called_once_with()


def test_Client_set_status(safe_tmpdir):
    """
    Ensure the GUI set_status API is called.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
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


def test_create_client_dir_permissions(tmpdir):
    '''
    Check that creating an app behaves appropriately with different
    permissions on the various directories needed for it to function.
    '''
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()

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


def test_Client_on_file_click_Submission(safe_tmpdir):
    """
    If the handler is passed a submission, check the download_submission
    function is the one called against the API.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    source = models.Source('source-uuid', 'testy-mctestface', False,
                           'mah pub key', 1, False, datetime.now())
    submission = models.Submission(source, 'submission-uuid', 1234,
                                   'myfile.doc.gpg', 'http://myserver/myfile')
    cl.call_api = mock.MagicMock()
    cl.api = mock.MagicMock()
    submission_sdk_object = mock.MagicMock()
    with mock.patch('sdclientapi.Submission') as mock_submission:
        mock_submission.return_value = submission_sdk_object
        cl.on_file_click(source, submission)
    cl.call_api.assert_called_once_with(
        cl.api.download_submission, cl.on_file_download,
        cl.on_download_timeout, submission_sdk_object,
        cl.data_dir, current_object=submission)


def test_Client_on_file_download_success(safe_tmpdir):
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.update_sources = mock.MagicMock()
    cl.api_runner = mock.MagicMock()
    test_filename = "my-file-location-msg.gpg"
    test_object_uuid = 'uuid-of-downloaded-object'
    cl.call_reset = mock.MagicMock()
    result_data = ('this-is-a-sha256-sum', test_filename)
    submission_db_object = mock.MagicMock()
    submission_db_object.uuid = test_object_uuid
    submission_db_object.filename = test_filename
    with mock.patch('securedrop_client.logic.storage') as mock_storage, \
            mock.patch('shutil.move'):
        cl.on_file_download(result_data, current_object=submission_db_object)
        mock_storage.mark_file_as_downloaded.assert_called_once_with(
            test_object_uuid, mock_session)

def test_Client_on_file_download_failure(safe_tmpdir):
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.update_sources = mock.MagicMock()
    cl.api_runner = mock.MagicMock()
    test_filename = "my-file-location-msg.gpg"
    cl.api_runner.result = ("", test_filename)
    cl.call_reset = mock.MagicMock()
    cl.set_status = mock.MagicMock()
    result_data = Exception('error message')
    submission_db_object = mock.MagicMock()
    submission_db_object.uuid = 'myuuid'
    submission_db_object.filename = 'filename'
    cl.on_file_download(result_data, current_object=submission_db_object)
    cl.set_status.assert_called_once_with(
        "The file download failed. Please try again.")


def test_Client_on_download_timeout(safe_tmpdir):
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    cl.update_sources = mock.MagicMock()
    cl.api_runner = mock.MagicMock()
    current_object = mock.MagicMock()
    test_filename = "my-file-location-msg.gpg"
    cl.api_runner.result = ("", test_filename)
    cl.call_reset = mock.MagicMock()
    cl.set_status = mock.MagicMock()
    cl.on_download_timeout(current_object)
    cl.set_status.assert_called_once_with(
        "The connection to the SecureDrop server timed out. Please try again.")


# This can be unfailed when this SDK change is merged and released:
# https://github.com/freedomofpress/securedrop-sdk/pull/32
@pytest.mark.xfail(reason="needs SDK change merged")
def test_Client_on_file_click_Reply(safe_tmpdir):
    """
    If the handler is passed a reply, check the download_reply
    function is the one called against the API.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session, str(safe_tmpdir))
    source = models.Source('source-uuid', 'testy-mctestface', False,
                           'mah pub key', 1, False, datetime.now())
    journalist = models.User('Testy mcTestface')
    reply = models.Reply('reply-uuid', journalist, source,
                         'my-reply.gpg', 123)  # Not a sdclientapi.Submission
    cl.call_api = mock.MagicMock()
    cl.api = mock.MagicMock()
    reply_sdk_object = mock.MagicMock()
    with mock.patch('sdclientapi.Reply') as mock_reply:
        mock_reply.return_value = reply_sdk_object
        cl.on_file_click(source, reply)
    cl.call_api.assert_called_once_with(cl.api.download_reply,
                                        cl.on_file_download,
                                        cl.on_download_timeout,
                                        reply_sdk_object,
                                        cl.data_dir, current_object=reply)
