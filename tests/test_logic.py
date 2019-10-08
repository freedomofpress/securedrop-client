"""
Make sure the Controller object, containing the application logic, behaves as
expected.
"""
import arrow
import os
import pytest

from PyQt5.QtCore import Qt
from sdclientapi import RequestTimeoutError
from tests import factory

from securedrop_client import storage, db
from securedrop_client.crypto import CryptoError
from securedrop_client.logic import APICallRunner, Controller
from securedrop_client.api_jobs.downloads import DownloadChecksumMismatchException
from securedrop_client.api_jobs.uploads import SendReplyJobError

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


def test_Controller_init(homedir, config, mocker, session_maker):
    """
    The passed in gui, app and session instances are correctly referenced and,
    where appropriate, have a reference back to the client.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller('http://localhost/', mock_gui, session_maker, homedir)
    assert co.hostname == 'http://localhost/'
    assert co.gui == mock_gui
    assert co.session_maker == session_maker
    assert co.api_threads == {}


def test_Controller_setup(homedir, config, mocker, session_maker):
    """
    Ensure the application is set up with the following default state:
    Using the `config` fixture to ensure the config is written to disk.
    """
    mocker.patch('securedrop_client.logic.QThread')
    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)
    co.export.moveToThread = mocker.MagicMock()
    co.update_sources = mocker.MagicMock()

    co.setup()

    co.gui.setup.assert_called_once_with(co)


def test_Controller_call_api(homedir, config, mocker, session_maker):
    """
    A new thread and APICallRunner is created / setup.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller('http://localhost', mock_gui, session_maker, homedir)

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


def test_Controller_login(homedir, config, mocker, session_maker):
    """
    Ensures the API is called in the expected manner for logging in the user
    given the username, password and 2fa token.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_api = mocker.patch('securedrop_client.logic.sdclientapi.API')

    co = Controller('http://localhost', mock_gui, session_maker, homedir)
    co.call_api = mocker.MagicMock()

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
    co.update_sources = mocker.MagicMock()

    co.login_offline_mode()

    assert co.call_api.called is False
    assert co.is_authenticated is False
    co.gui.show_main_window.assert_called_once_with()
    co.gui.hide_login.assert_called_once_with()
    co.update_sources.assert_called_once_with()


def test_Controller_on_authenticate_failure(homedir, config, mocker, session_maker):
    """
    If the server responds with a negative to the request to authenticate, make
    sure the user knows.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller('http://localhost', mock_gui, session_maker, homedir)

    result_data = Exception('oh no')
    co.on_authenticate_failure(result_data)

    mock_gui.show_login_error.\
        assert_called_once_with(error='There was a problem signing in. Please '
                                'verify your credentials and try again.')


def test_Controller_on_authenticate_success(homedir, config, mocker, session_maker):
    """
    Ensure the client syncs when the user successfully logs in.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_api_job_queue = mocker.patch("securedrop_client.logic.ApiJobQueue")
    co = Controller('http://localhost', mock_gui, session_maker, homedir)
    co.sync_api = mocker.MagicMock()
    co.api = mocker.MagicMock()
    co.call_api = mocker.MagicMock()
    co.resume_queues = mocker.MagicMock()
    login = mocker.patch.object(co.api_job_queue, 'login')
    current_user_api_result = {
        'uuid': 'mock_uuid',
        'username': 'mock_username',
        'first_name': 'mock_firstname',
        'last_name': 'mock_lastname'}
    co.api.get_current_user = mocker.MagicMock(return_value=(current_user_api_result))

    co.on_authenticate_success(True)

    co.sync_api.assert_called_once_with()
    assert mock_api_job_queue.called
    login.assert_called_with(co.api)
    co.resume_queues.assert_called_once_with()


def test_Controller_on_get_current_user_success(mocker, session_maker, session, homedir):
    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)
    co.api = mocker.MagicMock()
    co.call_api = mocker.MagicMock()
    user = factory.User(uuid='mock_uuid', username='mock_username')
    session.add(user)
    session.commit()
    current_user_api_result = {
        'uuid': 'mock_uuid',
        'username': 'mock_username',
        'first_name': 'firstname_mock',
        'last_name': 'lastname_mock'}

    co.on_get_current_user_success(current_user_api_result)

    user = session.query(db.User).filter_by(uuid='mock_uuid').one_or_none()
    assert user.firstname == 'firstname_mock'
    assert user.lastname == 'lastname_mock'
    assert user.fullname == 'firstname_mock lastname_mock'
    assert user.initials == 'fl'
    co.gui.show_main_window.assert_called_with(user)


def test_Controller_on_get_current_user_success_no_name(mocker, session_maker, session, homedir):
    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)
    co.api = mocker.MagicMock()
    co.call_api = mocker.MagicMock()
    user = factory.User(uuid='mock_uuid', username='mock_username')
    session.add(user)
    session.commit()
    storage = mocker.patch('securedrop_client.logic.storage')
    storage.update_and_get_user = mocker.MagicMock(return_value=user)
    current_user_api_result = {
        'uuid': 'mock_uuid',
        'username': 'mock_username',
        'first_name': None,
        'last_name': None}

    co.on_get_current_user_success(current_user_api_result)

    user = session.query(db.User).filter_by(uuid='mock_uuid').one_or_none()
    assert user.firstname is None
    assert user.lastname is None
    assert user.fullname == 'mock_username'
    assert user.initials == 'mo'
    co.gui.show_main_window.assert_called_with(user)


def test_Controller_on_get_current_user_failure(homedir, mocker, session_maker):
    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)
    result = Exception('oh no')

    co.on_get_current_user_failure(result)

    co.gui.show_login_error.assert_called_once_with(error='Could not find your account.')
    assert co.api is None


def test_Controller_completed_api_call_without_current_object(
    homedir,
    config,
    mocker,
    session_maker,
):
    """
    Ensure that cleanup is performed if an API call returns in the expected
    time.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller('http://localhost', mock_gui, session_maker, homedir)

    result = 'result'

    mock_thread = mocker.MagicMock()
    mock_runner = mocker.MagicMock()
    mock_runner.result = result
    mock_runner.current_object = None
    co.api_threads = {
        'thread_uuid': {
            'thread': mock_thread,
            'runner': mock_runner,
        }
    }
    mock_user_callback = mocker.MagicMock()

    co.completed_api_call('thread_uuid', mock_user_callback)

    mock_user_callback.assert_called_once_with(result)


def test_Controller_completed_api_call_with_current_object(homedir, config, mocker, session_maker):
    """
    Ensure that cleanup is performed if an API call returns in the expected
    time.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller('http://localhost', mock_gui, session_maker, homedir)

    result = 'result'
    current_object = 'current_object'

    mock_thread = mocker.MagicMock()
    mock_runner = mocker.MagicMock()
    mock_runner.result = result
    mock_runner.current_object = current_object
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
    mock_user_callback.assert_called_once_with(result,
                                               current_object=current_object)


def test_Controller_on_action_requiring_login(homedir, config, mocker, session_maker):
    """
    Ensure that when on_action_requiring_login is called, an error
    is shown in the GUI status area.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller('http://localhost', mock_gui, session_maker, homedir)

    co.on_action_requiring_login()

    mock_gui.update_error_status.assert_called_once_with(
        'You must sign in to perform this action.')


def test_Controller_authenticated_yes(homedir, config, mocker, session_maker):
    """
    If the API is authenticated return True.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller('http://localhost', mock_gui, session_maker, homedir)
    co.api = mocker.MagicMock()
    co.api.token = 'foo'

    assert co.authenticated() is True


def test_Controller_authenticated_no(homedir, config, mocker, session_maker):
    """
    If the API is authenticated return True.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller('http://localhost', mock_gui, session_maker, homedir)

    co.api = mocker.MagicMock()
    co.api.token = None

    assert co.authenticated() is False


def test_Controller_authenticated_no_api(homedir, config, mocker, session_maker):
    """
    If the API is authenticated return True.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller('http://localhost', mock_gui, session_maker, homedir)
    co.api = None

    assert co.authenticated() is False


def test_Controller_sync_api_not_authenticated(homedir, config, mocker, session_maker):
    """
    If the API isn't authenticated, don't sync.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller('http://localhost', mock_gui, session_maker, homedir)
    co.authenticated = mocker.MagicMock(return_value=False)
    co.call_api = mocker.MagicMock()

    co.sync_api()

    assert co.call_api.call_count == 0


def test_Controller_sync_api(homedir, config, mocker, session_maker):
    """
    Sync the API is authenticated.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller('http://localhost', mock_gui, session_maker, homedir)

    co.authenticated = mocker.MagicMock(return_value=True)
    co.call_api = mocker.MagicMock()

    co.sync_api()

    co.call_api.assert_called_once_with(storage.get_remote_data,
                                        co.on_sync_success,
                                        co.on_sync_failure,
                                        co.api)


def test_Controller_last_sync_with_file(homedir, config, mocker, session_maker):
    """
    The flag indicating the time of the last sync with the API is stored in a
    dotfile in the user's home directory. If such a file exists, ensure an
    "arrow" object (representing the date/time) is returned.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller('http://localhost', mock_gui, session_maker, homedir)

    timestamp = '2018-10-10 18:17:13+01:00'
    mocker.patch("builtins.open", mocker.mock_open(read_data=timestamp))

    result = co.last_sync()

    assert isinstance(result, arrow.Arrow)
    assert result.format() == timestamp


def test_Controller_last_sync_no_file(homedir, config, mocker, session_maker):
    """
    If there's no sync file, then just return None.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller('http://localhost', mock_gui, session_maker, homedir)

    mocker.patch("builtins.open", mocker.MagicMock(side_effect=Exception()))
    assert co.last_sync() is None


def test_Controller_on_sync_failure(homedir, config, mocker, session_maker):
    """
    If there's no result to syncing, then don't attempt to update local storage
    and perhaps implement some as-yet-undefined UI update.
    Using the `config` fixture to ensure the config is written to disk.
    """
    gui = mocker.MagicMock()
    co = Controller('http://localhost', gui, session_maker, homedir)
    exception = Exception('mock')  # Not the expected tuple.
    mock_storage = mocker.patch('securedrop_client.logic.storage')

    co.on_sync_failure(exception)

    assert mock_storage.update_local_storage.call_count == 0
    gui.update_error_status.assert_called_once_with(
        'The SecureDrop server cannot be reached.', duration=0, retry=True)


def test_Controller_on_sync_success(homedir, config, mocker):
    """
    If there's a result to syncing, then update local storage.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock(return_value=mock_session)

    co = Controller('http://localhost', mock_gui, mock_session_maker, homedir)
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
    mock_session_maker = mocker.MagicMock(return_value=mock_session)

    co = Controller('http://localhost', mock_gui, mock_session_maker, homedir)
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
    mock_session_maker = mocker.MagicMock(return_value=mock_session)

    co = Controller('http://localhost', mock_gui, mock_session_maker, homedir)
    co.update_sources = mocker.MagicMock()
    co.api_runner = mocker.MagicMock()

    mock_source = mocker.MagicMock()
    mock_source.key = {
        'type': 'PGP',
        'public': PUB_KEY,
        'fingerprint': 'ABCDEFGHIJKLMAO'
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


def test_Controller_update_sync(homedir, config, mocker, session_maker):
    """
    Cause the UI to update with the result of self.last_sync().
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, session_maker, homedir)
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
    mock_session_maker = mocker.MagicMock(return_value=mock_session)

    co = Controller('http://localhost', mock_gui, mock_session_maker, homedir)

    mock_storage = mocker.patch('securedrop_client.logic.storage')
    source_list = [factory.Source(last_updated=2), factory.Source(last_updated=1)]
    mock_storage.get_local_sources.return_value = source_list

    co.update_sources()

    mock_storage.get_local_sources.assert_called_once_with(mock_session)
    mock_gui.show_sources.assert_called_once_with(source_list)


def test_Controller_update_star_not_logged_in(homedir, config, mocker, session_maker):
    """
    Ensure that starring/unstarring a source when not logged in calls
    the method that displays an error status in the left sidebar.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, session_maker, homedir)
    source_db_object = mocker.MagicMock()
    co.on_action_requiring_login = mocker.MagicMock()
    co.api = None
    co.update_star(source_db_object)
    co.on_action_requiring_login.assert_called_with()


def test_Controller_on_update_star_success(homedir, config, mocker, session_maker):
    """
    If the starring occurs successfully, then a sync should occur to update
    locally.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, session_maker, homedir)
    result = True
    co.call_reset = mocker.MagicMock()
    co.sync_api = mocker.MagicMock()
    co.on_update_star_success(result)
    co.sync_api.assert_called_once_with()


def test_Controller_on_update_star_failed(homedir, config, mocker, session_maker):
    """
    If the starring does not occur properly, then an error should appear
    on the error status sidebar, and a sync will not occur.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, session_maker, homedir)
    result = Exception('boom')
    co.call_reset = mocker.MagicMock()
    co.sync_api = mocker.MagicMock()
    co.on_update_star_failure(result)
    co.sync_api.assert_not_called()
    mock_gui.update_error_status.assert_called_once_with('Failed to update star.')


def test_Controller_logout_success(homedir, config, mocker, session_maker):
    """
    Ensure the API is called on logout and if the API call succeeds,
    the API object is reset to None and the UI is set to logged out state.
    The message and reply threads should also have been reset.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, session_maker, homedir)
    co.api = mocker.MagicMock()
    co.api_job_queue = mocker.MagicMock()
    co.api_job_queue.logout = mocker.MagicMock()
    co.call_api = mocker.MagicMock()
    info_logger = mocker.patch('securedrop_client.logic.logging.info')
    logout_method = co.api.logout
    co.logout()
    co.call_api.assert_called_with(
        logout_method,
        co.on_logout_success,
        co.on_logout_failure)
    co.on_logout_success(True)
    assert co.api is None
    co.api_job_queue.logout.assert_called_once_with()
    co.gui.logout.assert_called_once_with()
    msg = 'Client logout successful'
    info_logger.assert_called_once_with(msg)


def test_Controller_logout_failure(homedir, config, mocker, session_maker):
    """
    Ensure the API is called on logout and if the API call fails,
    the API object is reset to None and the UI is set to logged out state.
    The message and reply threads should also have been reset.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, session_maker, homedir)
    co.api = mocker.MagicMock()
    co.api_job_queue = mocker.MagicMock()
    co.api_job_queue.logout = mocker.MagicMock()
    co.call_api = mocker.MagicMock()
    info_logger = mocker.patch('securedrop_client.logic.logging.info')
    logout_method = co.api.logout

    co.logout()

    co.call_api.assert_called_with(
        logout_method,
        co.on_logout_success,
        co.on_logout_failure)
    co.on_logout_failure(Exception())
    assert co.api is None
    co.api_job_queue.logout.assert_called_once_with()
    co.gui.logout.assert_called_once_with()
    msg = 'Client logout failure'
    info_logger.assert_called_once_with(msg)


def test_Controller_set_activity_status(homedir, config, mocker, session_maker):
    """
    Ensure the GUI set_status API is called.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, session_maker, homedir)
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


def test_create_client_dir_permissions(tmpdir, mocker, session_maker):
    '''
    Check that creating an app behaves appropriately with different
    permissions on the various directories needed for it to function.
    '''
    mock_gui = mocker.MagicMock()

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
            Controller('http://localhost', mock_gui, session_maker, sdc_home)

        if case['should_pass']:
            func()
        else:
            with pytest.raises(RuntimeError):
                func()

    # check that both mocks were called to ensure they aren't "dead code"
    assert mock_open.called
    assert mock_json.called


def test_Controller_on_file_download_Submission(homedir, config, session, mocker, session_maker):
    """
    If the handler is passed a Submission, check the download_submission
    function is the one called against the API.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, session_maker, homedir)
    co.api = 'this has a value'

    mock_success_signal = mocker.MagicMock()
    mock_failure_signal = mocker.MagicMock()
    mock_job = mocker.MagicMock(success_signal=mock_success_signal,
                                failure_signal=mock_failure_signal)
    mock_job_cls = mocker.patch(
        "securedrop_client.logic.FileDownloadJob", return_value=mock_job)
    mock_queue = mocker.patch.object(co, 'api_job_queue')

    source = factory.Source()
    file_ = factory.File(is_downloaded=None, is_decrypted=None, source=source)
    session.add(source)
    session.add(file_)
    session.commit()

    co.on_submission_download(db.File, file_.uuid)

    mock_job_cls.assert_called_once_with(
        file_.uuid,
        co.data_dir,
        co.gpg,
    )
    mock_queue.enqueue.assert_called_once_with(mock_job)
    mock_success_signal.connect.assert_called_once_with(
        co.on_file_download_success, type=Qt.QueuedConnection)
    mock_failure_signal.connect.assert_called_once_with(
        co.on_file_download_failure, type=Qt.QueuedConnection)


def test_Controller_on_file_download_Submission_no_auth(homedir, config, session,
                                                        mocker, session_maker):
    """If the controller is not authenticated, do not enqueue a download job"""
    mock_gui = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, session_maker, homedir)
    co.api = None

    mock_success_signal = mocker.MagicMock()
    mock_failure_signal = mocker.MagicMock()
    mock_job = mocker.MagicMock(success_signal=mock_success_signal,
                                failure_signal=mock_failure_signal)
    mock_job_cls = mocker.patch(
        "securedrop_client.logic.FileDownloadJob", return_value=mock_job)
    mock_queue = mocker.patch.object(co, 'api_job_queue')

    source = factory.Source()
    file_ = factory.File(is_downloaded=None, is_decrypted=None, source=source)
    session.add(source)
    session.add(file_)
    session.commit()

    co.on_submission_download(db.File, file_.uuid)

    assert not mock_job_cls.called
    assert not mock_queue.enqueue.called
    assert not mock_success_signal.connect.called
    assert not mock_failure_signal.connect.called


def test_Controller_on_file_downloaded_success(homedir, config, mocker, session_maker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()

    co = Controller('http://localhost', mock_gui, session_maker, homedir)

    # signal when file is downloaded
    mock_file_ready = mocker.patch.object(co, 'file_ready')
    mock_uuid = 'mock'

    co.on_file_download_success(mock_uuid)

    mock_file_ready.emit.assert_called_once_with(mock_uuid)


def test_Controller_on_file_downloaded_api_failure(homedir, config, mocker, session_maker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, session_maker, homedir)

    # signal when file is downloaded
    mock_file_ready = mocker.patch.object(co, 'file_ready')
    mock_set_status = mocker.patch.object(co, 'set_status')
    result_data = Exception('error message')

    co.on_file_download_failure(result_data)

    mock_set_status.assert_called_once_with("The file download failed. Please try again.")
    mock_file_ready.emit.assert_not_called()


def test_Controller_on_file_downloaded_checksum_failure(homedir, config, mocker, session_maker):
    '''
    Check that a failed download due to checksum resubmits the job and informs the user.
    '''

    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)

    file_ = factory.File(is_downloaded=None, is_decrypted=None, source=factory.Source())

    mock_set_status = mocker.patch.object(co, 'set_status')
    mock_file_ready = mocker.patch.object(co, 'file_ready')

    debug_logger = mocker.patch('securedrop_client.logic.logger.debug')
    co._submit_download_job = mocker.MagicMock()

    co.on_file_download_failure(DownloadChecksumMismatchException('bang!',
                                type(file_), file_.uuid))

    mock_file_ready.emit.assert_not_called()

    # Job should get resubmitted and we should log this is happening
    co._submit_download_job.call_count == 1
    debug_logger.call_args_list[0][0][0] == \
        'Failure due to checksum mismatch, retrying {}'.format(file_.uuid)

    # No status will be set if it's a file corruption issue, the file just gets
    # re-downloaded.
    mock_set_status.assert_not_called()


def test_Controller_on_file_open(homedir, config, mocker, session, session_maker, source):
    """
    If running on Qubes, a new QProcess with the expected command and args should be started.
    Using the `config` fixture to ensure the config is written to disk.
    """
    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)
    co.qubes = True
    file = factory.File(source=source['source'])
    session.add(file)
    session.commit()
    mocker.patch('securedrop_client.logic.Controller.get_file', return_value=file)
    mocker.patch('os.path.exists', return_value=True)
    mocker.patch('os.remove')
    mock_subprocess = mocker.MagicMock()
    mock_process = mocker.MagicMock(return_value=mock_subprocess)
    mocker.patch('securedrop_client.logic.QProcess', mock_process)
    mock_link = mocker.patch('os.link')

    co.on_file_open(file.uuid)

    co.get_file.assert_called_once_with(file.uuid)
    mock_process.assert_called_once_with(co)
    assert mock_subprocess.start.call_count == 1
    assert mock_link.call_count == 1


def test_Controller_on_file_open_existing_link_problem(
        homedir, config, mocker, session, session_maker, source, caplog):
    """
    Test that open works if the link to the original filename exists.
    """
    mock_gui = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, session_maker, homedir)
    co.proxy = True

    submission = factory.File(source=source['source'])
    session.add(submission)
    session.commit()

    mock_subprocess = mocker.MagicMock()
    mock_process = mocker.MagicMock(return_value=mock_subprocess)
    mock_exists = mocker.patch('os.path.exists', return_value=True)
    mock_link = mocker.patch('os.link')
    mocker.patch('securedrop_client.logic.QProcess', mock_process)
    mock_remove = mocker.patch('os.remove')

    co.on_file_open(submission.uuid)
    mock_process.assert_called_once_with(co)
    assert mock_subprocess.start.call_count == 1
    assert mock_exists.call_count == 1
    assert mock_link.call_count == 1
    assert mock_remove.call_count == 1


def test_Controller_on_file_open_file_missing(mocker, homedir, session_maker):
    """
    When file does not exist, test that we log and send status update to user.
    """
    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)
    mocker.patch('securedrop_client.logic.Controller.get_file')
    mocker.patch('os.path.exists', return_value=False)

    co.on_file_open('mock_uuid')

    msg = 'Export failed. File no longer exists in the data directory.'
    co.gui.update_error_status.assert_called_once_with(msg)


def test_Controller_download_new_replies_with_new_reply(mocker, session, session_maker, homedir):
    """
    Test that `download_new_replies` enqueues a job, connects to the right slots, and sets a
    user-facing status message when a new reply is found.
    """
    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)
    reply = factory.Reply(source=factory.Source())
    mocker.patch('securedrop_client.storage.find_new_replies', return_value=[reply])
    success_signal = mocker.MagicMock()
    failure_signal = mocker.MagicMock()
    job = mocker.MagicMock(success_signal=success_signal, failure_signal=failure_signal)
    mocker.patch("securedrop_client.logic.ReplyDownloadJob", return_value=job)
    api_job_queue = mocker.patch.object(co, 'api_job_queue')

    co.download_new_replies()

    api_job_queue.enqueue.assert_called_once_with(job)
    success_signal.connect.assert_called_once_with(
        co.on_reply_download_success, type=Qt.QueuedConnection)
    failure_signal.connect.assert_called_once_with(
        co.on_reply_download_failure, type=Qt.QueuedConnection)


def test_Controller_download_new_replies_without_replies(mocker, session, session_maker, homedir):
    """
    Test that `download_new_replies` does not enqueue any jobs or connect to slots or set a
    user-facing status message when there are no new replies found.
    """
    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)
    mocker.patch('securedrop_client.storage.find_new_replies', return_value=[])
    success_signal = mocker.MagicMock()
    failure_signal = mocker.MagicMock()
    job = mocker.MagicMock(success_signal=success_signal, failure_signal=failure_signal)
    mocker.patch("securedrop_client.logic.ReplyDownloadJob", return_value=job)
    api_job_queue = mocker.patch.object(co, 'api_job_queue')
    set_status = mocker.patch.object(co, 'set_status')

    co.download_new_replies()

    api_job_queue.enqueue.assert_not_called()
    success_signal.connect.assert_not_called()
    failure_signal.connect.assert_not_called()
    set_status.assert_not_called()


def test_Controller_on_reply_downloaded_success(mocker, homedir, session_maker):
    """
    Check that a successful download emits proper signal.
    """
    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)
    reply_ready = mocker.patch.object(co, 'reply_ready')
    reply = factory.Message(source=factory.Source())
    mocker.patch('securedrop_client.storage.get_reply', return_value=reply)

    co.on_reply_download_success(reply.uuid)

    reply_ready.emit.assert_called_once_with(reply.uuid, reply.content)


def test_Controller_on_reply_downloaded_failure(mocker, homedir, session_maker):
    """
    Check that a failed download informs the user.
    """
    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)
    reply_ready = mocker.patch.object(co, 'reply_ready')
    reply = factory.Reply(source=factory.Source())
    mocker.patch('securedrop_client.storage.get_reply', return_value=reply)
    debug_logger = mocker.patch('securedrop_client.logic.logger.debug')
    co._submit_download_job = mocker.MagicMock()

    co.on_reply_download_failure('mock_exception')

    debug_logger.assert_called_once_with('Failed to download reply: mock_exception')
    reply_ready.emit.assert_not_called()

    # Job should not get automatically resubmitted if the failure was generic
    co._submit_download_job.assert_not_called()


def test_Controller_on_reply_downloaded_checksum_failure(mocker, homedir, session_maker):
    """
    Check that a failed download due to checksum resubmits the job and informs the user.
    """
    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)
    reply_ready = mocker.patch.object(co, 'reply_ready')
    reply = factory.Reply(source=factory.Source())
    mocker.patch('securedrop_client.storage.get_reply', return_value=reply)
    debug_logger = mocker.patch('securedrop_client.logic.logger.debug')
    co._submit_download_job = mocker.MagicMock()

    co.on_reply_download_failure(DownloadChecksumMismatchException('bang!',
                                 type(reply), reply.uuid))

    debug_logger.call_args_list[0][0][0] == 'Failed to download reply: bang!'
    reply_ready.emit.assert_not_called()

    # Job should get resubmitted and we should log this is happening
    co._submit_download_job.call_count == 1
    debug_logger.call_args_list[1][0][0] == \
        'Failure due to checksum mismatch, retrying {}'.format(reply.uuid)


def test_Controller_download_new_messages_with_new_message(mocker, session, session_maker, homedir):
    """
    Test that `download_new_messages` enqueues a job, connects to the right slots, and sets a
    usre-facing status message when a new message is found.
    """
    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)
    message = factory.Message(source=factory.Source())
    mocker.patch('securedrop_client.storage.find_new_messages', return_value=[message])
    success_signal = mocker.MagicMock()
    failure_signal = mocker.MagicMock()
    job = mocker.MagicMock(success_signal=success_signal, failure_signal=failure_signal)
    mocker.patch("securedrop_client.logic.MessageDownloadJob", return_value=job)
    api_job_queue = mocker.patch.object(co, 'api_job_queue')
    set_status = mocker.patch.object(co, 'set_status')

    co.download_new_messages()

    api_job_queue.enqueue.assert_called_once_with(job)
    success_signal.connect.assert_called_once_with(
        co.on_message_download_success, type=Qt.QueuedConnection)
    failure_signal.connect.assert_called_once_with(
        co.on_message_download_failure, type=Qt.QueuedConnection)
    set_status.assert_called_once_with("Downloading new messages")


def test_Controller_download_new_messages_without_messages(mocker, session, session_maker, homedir):
    """
    Test that `download_new_messages` does not enqueue any jobs or connect to slots or set a
    user-facing status message when there are no new messages found.
    """
    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)
    mocker.patch('securedrop_client.storage.find_new_messages', return_value=[])
    success_signal = mocker.MagicMock()
    failure_signal = mocker.MagicMock()
    job = mocker.MagicMock(success_signal=success_signal, failure_signal=failure_signal)
    mocker.patch("securedrop_client.logic.MessageDownloadJob", return_value=job)
    api_job_queue = mocker.patch.object(co, 'api_job_queue')
    set_status = mocker.patch.object(co, 'set_status')

    co.download_new_messages()

    api_job_queue.enqueue.assert_not_called()
    success_signal.connect.assert_not_called()
    failure_signal.connect.assert_not_called()
    set_status.assert_not_called()


def test_Controller_on_message_downloaded_success(mocker, homedir, session_maker):
    """
    Check that a successful download emits proper signal.
    """
    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)
    message_ready = mocker.patch.object(co, 'message_ready')
    message = factory.Message(source=factory.Source())
    mocker.patch('securedrop_client.storage.get_message', return_value=message)

    co.on_message_download_success(message.uuid)

    message_ready.emit.assert_called_once_with(message.uuid, message.content)


def test_Controller_on_message_downloaded_failure(mocker, homedir, session_maker):
    """
    Check that a failed download informs the user.
    """
    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)
    message_ready = mocker.patch.object(co, 'message_ready')
    message = factory.Message(source=factory.Source())
    mocker.patch('securedrop_client.storage.get_message', return_value=message)
    co._submit_download_job = mocker.MagicMock()
    debug_logger = mocker.patch('securedrop_client.logic.logger.debug')

    co.on_message_download_failure('mock_exception')

    debug_logger.assert_called_once_with('Failed to download message: mock_exception')
    message_ready.emit.assert_not_called()

    # Job should not get automatically resubmitted if the failure was generic
    co._submit_download_job.assert_not_called()


def test_Controller_on_message_downloaded_checksum_failure(mocker, homedir, session_maker):
    """
    Check that a failed download due to checksum resubmits the job and informs the user.
    """
    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)
    message_ready = mocker.patch.object(co, 'message_ready')
    message = factory.Message(source=factory.Source())
    mocker.patch('securedrop_client.storage.get_message', return_value=message)
    co._submit_download_job = mocker.MagicMock()
    debug_logger = mocker.patch('securedrop_client.logic.logger.debug')

    co.on_message_download_failure(DownloadChecksumMismatchException('bang!',
                                   type(message), message.uuid))

    debug_logger.call_args_list[0][0][0] == 'Failed to download message: bang!'
    message_ready.emit.assert_not_called()

    # Job should get resubmitted and we should log this is happening
    co._submit_download_job.call_count == 1
    debug_logger.call_args_list[1][0][0] == \
        'Failure due to checksum mismatch, retrying {}'.format(message.uuid)


def test_Controller_on_delete_source_success(homedir, config, mocker, session_maker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, session_maker, homedir)
    co.sync_api = mocker.MagicMock()
    co.on_delete_source_success(True)
    co.sync_api.assert_called_with()


def test_Controller_on_delete_source_failure(homedir, config, mocker, session_maker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, session_maker, homedir)
    co.sync_api = mocker.MagicMock()
    co.on_delete_source_failure(Exception())
    co.gui.update_error_status.assert_called_with('Failed to delete source at server')


def test_Controller_delete_source(homedir, config, mocker, session_maker):
    '''
    Using the `config` fixture to ensure the config is written to disk.
    '''
    mock_gui = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, session_maker, homedir)
    co.call_api = mocker.MagicMock()
    co.api = mocker.MagicMock()
    co.delete_source(mock_source)
    co.call_api.assert_called_with(
        co.api.delete_source,
        co.on_delete_source_success,
        co.on_delete_source_failure,
        mock_source
    )


def test_Controller_send_reply_success(homedir, config, mocker, session_maker, session):
    '''
    Check that a SendReplyJob is submitted to the queue when send_reply is called.
    '''
    mock_gui = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, session_maker, homedir)

    mock_success_signal = mocker.MagicMock()
    mock_failure_signal = mocker.MagicMock()
    mock_job = mocker.MagicMock(success_signal=mock_success_signal,
                                failure_signal=mock_failure_signal)
    mock_job_cls = mocker.patch(
        "securedrop_client.logic.SendReplyJob", return_value=mock_job)
    mock_queue = mocker.patch.object(co, 'api_job_queue')

    source = factory.Source()
    session.add(source)
    session.commit()

    msg_uuid = 'xyz456'
    msg = 'wat'

    co.send_reply(source.uuid, msg_uuid, msg)

    mock_job_cls.assert_called_once_with(
        source.uuid,
        msg_uuid,
        msg,
        co.gpg,
    )

    mock_queue.enqueue.assert_called_once_with(mock_job)
    mock_success_signal.connect.assert_called_once_with(
        co.on_reply_success, type=Qt.QueuedConnection)
    mock_failure_signal.connect.assert_called_once_with(
        co.on_reply_failure, type=Qt.QueuedConnection)


def test_Controller_on_reply_success(homedir, mocker, session_maker, session):
    '''
    Check that when the method is called, the client emits the correct signal.
    '''
    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)
    mocker.patch.object(co, 'sync_api')
    reply_succeeded = mocker.patch.object(co, 'reply_succeeded')
    reply_failed = mocker.patch.object(co, 'reply_failed')
    reply = factory.Reply(source=factory.Source())
    debug_logger = mocker.patch('securedrop_client.logic.logger.debug')

    co.on_reply_success(reply.uuid)

    assert debug_logger.call_args_list[0][0][0] == '{} sent successfully'.format(reply.uuid)
    reply_succeeded.emit.assert_called_once_with(reply.uuid)
    reply_failed.emit.assert_not_called()
    co.sync_api.assert_called_once_with()


def test_Controller_on_reply_failure(homedir, mocker, session_maker):
    '''
    Check that when the method is called, the client emits the correct signal.
    '''
    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)
    reply_succeeded = mocker.patch.object(co, 'reply_succeeded')
    reply_failed = mocker.patch.object(co, 'reply_failed')
    debug_logger = mocker.patch('securedrop_client.logic.logger.debug')

    exception = SendReplyJobError('mock_error_message', 'mock_reply_uuid')
    co.on_reply_failure(exception)

    debug_logger.assert_called_once_with('{} failed to send'.format('mock_reply_uuid'))
    reply_failed.emit.assert_called_once_with('mock_reply_uuid')
    reply_succeeded.emit.assert_not_called()


def test_Controller_is_authenticated_property(homedir, mocker, session_maker):
    '''
    Check that the @property `is_authenticated`:
      - Cannot be deleted
      - Emits the correct signals when updated
      - Sets internal state to ensure signals are only set when the state changes
    '''
    mock_gui = mocker.MagicMock()

    co = Controller('http://localhost', mock_gui, session_maker, homedir)
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


def test_Controller_resume_queues(homedir, mocker, session_maker):
    co = Controller('http://localhost', mocker.MagicMock(), session_maker, homedir)
    co.api_job_queue = mocker.MagicMock()
    co.resume_queues()
    co.api_job_queue.resume_queues.assert_called_once_with()


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


def test_Controller_on_queue_paused(homedir, config, mocker, session_maker):
    '''
    Check that a paused queue is communicated to the user via the error status bar with retry option
    '''
    mock_gui = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, session_maker, homedir)
    co.api = 'mock'
    co.on_queue_paused()
    mock_gui.update_error_status.assert_called_once_with(
        'The SecureDrop server cannot be reached.', duration=0, retry=True)


def test_Controller_on_queue_paused_when_logged_out(homedir, config, mocker, session_maker):
    '''
    Check that a paused queue is communicated to the user via the error status bar. There should not
    be a retry option displayed to the user
    '''
    mock_gui = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, session_maker, homedir)
    co.api = None
    co.on_queue_paused()
    mock_gui.update_error_status.assert_called_once_with('The SecureDrop server cannot be reached.')


def test_Controller_call_update_star_success(homedir, config, mocker, session_maker, session):
    '''
    Check that a UpdateStar is submitted to the queue when update_star is called.
    '''
    mock_gui = mocker.MagicMock()
    co = Controller('http://localhost', mock_gui, session_maker, homedir)
    co.call_api = mocker.MagicMock()
    co.api = mocker.MagicMock()

    mock_success_signal = mocker.MagicMock()
    mock_failure_signal = mocker.MagicMock()
    mock_job = mocker.MagicMock(success_signal=mock_success_signal,
                                failure_signal=mock_failure_signal)
    mock_job_cls = mocker.patch(
        "securedrop_client.logic.UpdateStarJob", return_value=mock_job)
    mock_queue = mocker.patch.object(co, 'api_job_queue')

    source = factory.Source()
    session.add(source)
    session.commit()

    co.update_star(source)

    mock_job_cls.assert_called_once_with(
        source.uuid,
        source.is_starred
    )

    mock_queue.enqueue.assert_called_once_with(mock_job)
    mock_success_signal.connect.assert_called_once_with(
        co.on_update_star_success, type=Qt.QueuedConnection)
    mock_failure_signal.connect.assert_called_once_with(
        co.on_update_star_failure, type=Qt.QueuedConnection)


def test_Controller_run_export_preflight_checks(homedir, mocker):
    co = Controller('http://localhost', mocker.MagicMock(), mocker.MagicMock(), homedir)
    co.export = mocker.MagicMock()
    co.export.begin_preflight_check = mocker.MagicMock()
    co.export.begin_preflight_check.emit = mocker.MagicMock()

    co.run_export_preflight_checks()

    co.export.begin_usb_export.emit.call_count == 1


def test_Controller_run_export_preflight_checks_not_qubes(homedir, mocker):
    co = Controller('http://localhost', mocker.MagicMock(), mocker.MagicMock(), homedir)
    co.qubes = False
    co.export = mocker.MagicMock()
    co.export.begin_preflight_check = mocker.MagicMock()
    co.export.begin_preflight_check.emit = mocker.MagicMock()

    co.run_export_preflight_checks()

    co.export.begin_usb_export.emit.call_count == 0


def test_Controller_export_file_to_usb_drive(homedir, mocker, session):
    co = Controller('http://localhost', mocker.MagicMock(), mocker.MagicMock(), homedir)
    co.export = mocker.MagicMock()
    co.export.begin_usb_export = mocker.MagicMock()
    co.export.begin_usb_export.emit = mocker.MagicMock()
    file = factory.File(source=factory.Source(), original_filename='mock_filename')
    session.add(file)
    session.commit()
    mocker.patch('securedrop_client.logic.Controller.get_file', return_value=file)
    mocker.patch('os.path.exists', return_value=True)

    co.export_file_to_usb_drive(file.uuid, 'mock passphrase')

    # Signal to begin the USB export should be emitted
    co.export.begin_usb_export.emit.call_count == 1


def test_Controller_export_file_to_usb_drive_failed_file_missing(homedir, mocker, session):
    debug_logger = mocker.patch('securedrop_client.logic.logger.debug')
    co = Controller('http://localhost', mocker.MagicMock(), mocker.MagicMock(), homedir)
    co.export = mocker.MagicMock()
    file = factory.File(source=factory.Source(), original_filename='mock_filename')
    session.add(file)
    session.commit()
    mocker.patch('securedrop_client.logic.Controller.get_file', return_value=file)

    co.export_file_to_usb_drive(file.uuid, 'mock passphrase')

    debug_logger.call_args_list[0][0][0] == 'Exporting {}'.format(file.original_filename)
    failure_message = 'Export failed. File no longer exists in the data directory'
    debug_logger.call_args_list[1][0][0] == failure_message


def test_Controller_export_file_to_usb_drive_not_qubes(homedir, mocker, session):
    co = Controller('http://localhost', mocker.MagicMock(), mocker.MagicMock(), homedir)
    co.qubes = False
    co.export = mocker.MagicMock()
    co.export.begin_usb_export = mocker.MagicMock()
    co.export.begin_usb_export.emit = mocker.MagicMock()
    file = factory.File(source=factory.Source(), original_filename='mock_filename')
    session.add(file)
    session.commit()
    mocker.patch('securedrop_client.logic.Controller.get_file', return_value=file)

    co.export_file_to_usb_drive(file.uuid, 'mock passphrase')

    co.export.send_file_to_usb_device.assert_not_called()
    co.export.begin_usb_export.emit.call_count == 0
