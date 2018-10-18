"""
Make sure the Client object, containing the application logic, behaves as
expected.
"""
import arrow
from securedrop_client import storage
from securedrop_client.logic import APICallRunner, Client
from unittest import mock


def test_APICallRunner_init():
    """
    Ensure everything is set up as expected.
    """
    mock_api_call = mock.MagicMock()
    cr = APICallRunner(mock_api_call, 'foo', bar='baz')
    assert cr.api_call == mock_api_call
    assert cr.args == ('foo', )
    assert cr.kwargs == {'bar': 'baz', }


def test_APICallRunner_call_api():
    """
    A result is obtained so emit True and put the result in self.result.
    """
    mock_api_call = mock.MagicMock(return_value='foo')
    mock_api_call.__name__ = 'my_function'
    cr = APICallRunner(mock_api_call, 'foo', bar='baz')
    cr.call_finished = mock.MagicMock()
    with mock.patch('securedrop_client.logic.QTimer') as mock_timer:
        cr.call_api()
    assert cr.timer == mock_timer()
    assert cr.result == 'foo'
    cr.call_finished.emit.assert_called_once_with(True)


def test_APICallRunner_with_exception():
    """
    An exception has occured so emit False.
    """
    ex = Exception('boom')
    mock_api_call = mock.MagicMock(side_effect=ex)
    mock_api_call.__name__ = 'my_function'
    cr = APICallRunner(mock_api_call, 'foo', bar='baz')
    cr.call_finished = mock.MagicMock()
    with mock.patch('securedrop_client.logic.QTimer') as mock_timer:
        cr.call_api()
    assert cr.result == ex
    cr.call_finished.emit.assert_called_once_with(False)


def test_APICallRunner_on_cancel_timeout():
    """
    Ensure the timer's stop method is called.
    """
    mock_api_call = mock.MagicMock()
    cr = APICallRunner(mock_api_call, 'foo', bar='baz')
    cr.timer = mock.MagicMock()
    cr.on_cancel_timeout()
    cr.timer.stop.assert_called_once_with()


def test_Client_init():
    """
    The passed in gui, app and session instances are correctly referenced and,
    where appropriate, have a reference back to the client.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost/', mock_gui, mock_session)
    assert cl.hostname == 'http://localhost/'
    assert cl.gui == mock_gui
    assert cl.session == mock_session
    assert cl.api_thread is None


def test_Client_setup():
    """
    Ensure the application is set up with the following default state:
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    cl.update_sources = mock.MagicMock()
    cl.setup()
    cl.gui.setup.assert_called_once_with(cl)
    cl.update_sources.assert_called_once_with()
    cl.gui.show_conversation_for.assert_called_once_with()


def test_Client_call_api_existing_thread():
    """
    The client will ignore attempt to call API if an existing request is in
    progress.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    cl.api_thread = True
    cl.call_api(mock.MagicMock(), mock.MagicMock(), mock.MagicMock())
    assert cl.api_thread is True


def test_Client_call_api():
    """
    A new thread and APICallRunner is created / setup.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    cl.finish_api_call = mock.MagicMock()
    with mock.patch('securedrop_client.logic.QThread') as mock_qthread, \
            mock.patch('securedrop_client.logic.APICallRunner') as mock_runner:
        mock_api_call = mock.MagicMock()
        mock_callback = mock.MagicMock()
        mock_timeout = mock.MagicMock()
        cl.call_api(mock_api_call, mock_callback, mock_timeout, 'foo',
                    bar='baz')
        cl.api_thread.started.connect.\
            assert_called_once_with(cl.api_runner.call_api)
        cl.api_thread.finished.connect.\
            assert_called_once_with(cl.call_reset)
        cl.api_thread.start.assert_called_once_with()
        cl.api_runner.moveToThread.assert_called_once_with(cl.api_thread)
        cl.api_runner.call_finished.connect.\
            assert_called_once_with(mock_callback)
        cl.api_runner.timeout.connect.assert_called_once_with(mock_timeout)
        cl.finish_api_call.connect(cl.api_runner.on_cancel_timeout)


def test_Client_call_reset_no_thread():
    """
    The client will ignore an attempt to reset an API call is there's no such
    call "in flight".
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    cl.finish_api_call = mock.MagicMock()
    cl.api_thread = None
    cl.call_reset()
    assert cl.finish_api_call.emit.call_count == 0


def test_Client_call_reset():
    """
    Call reset emits the expected signal and resets the state of client
    attributes.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    cl.finish_api_call = mock.MagicMock()
    cl.api_thread = True
    cl.call_reset()
    assert cl.finish_api_call.emit.call_count == 1
    assert cl.api_runner is None
    assert cl.api_thread is None


def test_Client_login():
    """
    Ensures the API is called in the expected manner for logging in the user
    given the username, password and 2fa token.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    cl.call_api = mock.MagicMock()
    with mock.patch('securedrop_client.logic.sdclientapi.API') as mock_api:
        cl.login('username', 'password', '123456')
        cl.call_api.assert_called_once_with(mock_api().authenticate,
                                            cl.on_authenticate,
                                            cl.on_login_timeout)


def test_Client_on_authenticate_failed():
    """
    If the server responds with a negative to the request to authenticate, make
    sure the user knows.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    cl.on_authenticate(False)
    mock_gui.show_login.assert_called_once_with(error='There was a problem '
                                                'logging in. Please try '
                                                'again.')


def test_Client_on_authenticate_ok():
    """
    Ensure the client syncs when the user successfully logs in.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    cl.sync_api = mock.MagicMock()
    cl.api = mock.MagicMock()
    cl.api.username = 'test'
    cl.on_authenticate(True)
    cl.sync_api.assert_called_once_with()
    cl.gui.set_logged_in_as.assert_called_once_with('test')


def test_Client_on_login_timeout():
    """
    Reset the form if the API call times out.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    cl.call_reset = mock.MagicMock()
    cl.on_login_timeout()
    cl.call_reset.assert_called_once_with()
    mock_gui.show_login.assert_called_once_with(error='The connection to '
                                                'SecureDrop timed out. Please '
                                                'try again.')


def test_Client_authenticated_yes():
    """
    If the API is authenticated return True.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    cl.api = mock.MagicMock()
    cl.api.token = {'token': 'foo'}
    assert cl.authenticated() is True


def test_Client_authenticated_no():
    """
    If the API is authenticated return True.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    cl.api = mock.MagicMock()
    cl.api.token = {'token': ''}
    assert cl.authenticated() is False


def test_Client_authenticated_no_api():
    """
    If the API is authenticated return True.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    cl.api = None
    assert cl.authenticated() is False


def test_Client_sync_api_not_authenticated():
    """
    If the API isn't authenticated, don't sync.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    cl.authenticated = mock.MagicMock(return_value=False)
    cl.call_api = mock.MagicMock()
    cl.sync_api()
    assert cl.call_api.call_count == 0


def test_Client_sync_api():
    """
    Sync the API is authenticated.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    cl.authenticated = mock.MagicMock(return_value=True)
    cl.call_api = mock.MagicMock()
    cl.sync_api()
    cl.call_api.assert_called_once_with(storage.get_remote_data, cl.on_synced,
                                        cl.on_login_timeout, cl.api)


def test_Client_last_sync_with_file():
    """
    The flag indicating the time of the last sync with the API is stored in a
    dotfile in the user's home directory. If such a file exists, ensure an
    "arror" object (representing the date/time) is returned.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    timestamp = '2018-10-10 18:17:13+01:00'
    with mock.patch("builtins.open", mock.mock_open(read_data=timestamp)):
        result = cl.last_sync()
        assert isinstance(result, arrow.Arrow)
        assert result.format() == timestamp


def test_Client_last_sync_no_file():
    """
    If there's no sync file, then just return None.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    with mock.patch("builtins.open", mock.MagicMock(side_effect=Exception())):
        assert cl.last_sync() is None


def test_Client_on_synced_no_result():
    """
    If there's no result to syncing, then don't attempt to update local storage
    and perhaps implement some as-yet-undefined UI update.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    cl.update_sources = mock.MagicMock()
    with mock.patch('securedrop_client.logic.storage') as mock_storage:
        cl.on_synced(False)
        assert mock_storage.update_local_storage.call_count == 0
    cl.update_sources.assert_called_once_with()


def test_Client_on_synced_with_result():
    """
    If there's a result to syncing, then update local storage.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    cl.update_sources = mock.MagicMock()
    cl.api_runner = mock.MagicMock()
    cl.api_runner.result = (1, 2, 3, )
    cl.call_reset = mock.MagicMock()
    with mock.patch('securedrop_client.logic.storage') as mock_storage:
        cl.on_synced(True)
        cl.call_reset.assert_called_once_with()
        mock_storage.update_local_storage.assert_called_once_with(mock_session,
                                                                  1, 2, 3)
    cl.update_sources.assert_called_once_with()


def test_Client_update_sync():
    """
    Cause the UI to update with the result of self.last_sync().
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    cl.last_sync = mock.MagicMock()
    cl.update_sync()
    assert cl.last_sync.call_count == 1
    cl.gui.show_sync.assert_called_once_with(cl.last_sync())


def test_Client_update_sources():
    """
    Ensure the UI displays a list of the available sources from local data
    store.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    with mock.patch('securedrop_client.logic.storage') as mock_storage:
        mock_storage.get_local_sources.return_value = (1, 2, 3)
        cl.update_sources()
        mock_storage.get_local_sources.assert_called_once_with(mock_session)
        mock_gui.show_sources.assert_called_once_with([1, 2, 3])


def test_Client_logout():
    """
    The API is reset to None and the UI is set to logged out state.
    """
    mock_gui = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client('http://localhost', mock_gui, mock_session)
    cl.api = mock.MagicMock()
    cl.logout()
    assert cl.api is None
    cl.gui.logout.assert_called_once_with()
