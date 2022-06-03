"""
Make sure the Controller object, containing the application logic, behaves as
expected.
"""
import datetime
import logging
import os
from gettext import gettext as _
from typing import Type
from unittest.mock import Mock, call

import arrow
import pytest
import sqlalchemy.orm.exc
from PyQt5.QtCore import Qt
from PyQt5.QtTest import QSignalSpy
from sdclientapi import AuthError, RequestTimeoutError, ServerConnectionError
from sqlalchemy.orm import attributes

from securedrop_client import db, state
from securedrop_client.api_jobs.base import ApiInaccessibleError
from securedrop_client.api_jobs.downloads import (
    DownloadChecksumMismatchException,
    DownloadDecryptionException,
    DownloadException,
)
from securedrop_client.api_jobs.sources import (
    DeleteConversationJobException,
    DeleteSourceJobException,
)
from securedrop_client.api_jobs.updatestar import UpdateStarJobError, UpdateStarJobTimeoutError
from securedrop_client.api_jobs.uploads import SendReplyJobError, SendReplyJobTimeoutError
from securedrop_client.logic import TIME_BETWEEN_SHOWING_LAST_SYNC_MS, APICallRunner, Controller
from tests import factory

with open(os.path.join(os.path.dirname(__file__), "files", "test-key.gpg.pub.asc")) as f:
    PUB_KEY = f.read()


def test_APICallRunner_init(mocker):
    """
    Ensure everything is set up as expected.
    """
    mock_api_call = mocker.MagicMock()
    mock_current_object = mocker.MagicMock()
    cr = APICallRunner(mock_api_call, mock_current_object, "foo", bar="baz")
    assert cr.api_call == mock_api_call
    assert cr.current_object == mock_current_object
    assert cr.args == ("foo",)
    assert cr.kwargs == {"bar": "baz"}


def test_APICallRunner_call_api(mocker):
    """
    A result is obtained so emit True and put the result in self.result.
    """
    mock_api_call = mocker.MagicMock(return_value="foo")
    mock_api_call.__name__ = "my_function"
    mock_current_object = mocker.MagicMock()
    cr = APICallRunner(mock_api_call, mock_current_object, "foo", bar="baz")
    call_succeeded_emissions = QSignalSpy(cr.call_succeeded)
    cr.call_api()
    assert cr.result == "foo"
    assert len(call_succeeded_emissions) == 1


def test_APICallRunner_with_exception(mocker):
    """
    An exception has occured so emit False.
    """
    ex = Exception("boom")
    mock_api_call = mocker.MagicMock(side_effect=ex)
    mock_api_call.__name__ = "my_function"
    mock_current_object = mocker.MagicMock()
    cr = APICallRunner(mock_api_call, mock_current_object, "foo", bar="baz")
    call_failed_emissions = QSignalSpy(cr.call_failed)
    mocker.patch("securedrop_client.logic.QTimer")
    cr.call_api()
    assert cr.result == ex
    assert len(call_failed_emissions) == 1


def test_Controller_init(homedir, config, mocker, session_maker):
    """
    The passed in gui, app and session instances are correctly referenced and,
    where appropriate, have a reference back to the client.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    # Ensure a sync_flag file with insecure perms is updated with the expected perms
    insecure_sync_flag_path = os.path.join(homedir, "sync_flag")
    with open(insecure_sync_flag_path, "w"):
        os.chmod(insecure_sync_flag_path, 0o100644)
        assert oct(os.stat(insecure_sync_flag_path).st_mode) == "0o100644"  # sanity check
        co = Controller("http://localhost/", mock_gui, session_maker, homedir, None)
        assert co.hostname == "http://localhost/"
        assert co.gui == mock_gui
        assert co.session_maker == session_maker
        assert co.api_threads == {}
        assert co.last_sync_filepath == insecure_sync_flag_path
        assert oct(os.stat(co.last_sync_filepath).st_mode) == "0o100600"


def test_Controller_setup(homedir, config, mocker, session_maker, session):
    """
    Ensure the application is set up with the following default state:
    Using the `config` fixture to ensure the config is written to disk.
    """
    mocker.patch("securedrop_client.logic.QThread")
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
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

    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)

    co.finish_api_call = mocker.MagicMock()
    mocker.patch("securedrop_client.logic.QThread")
    mocker.patch("securedrop_client.logic.APICallRunner")
    mocker.patch("securedrop_client.logic.QTimer")
    mock_api_call = mocker.MagicMock()
    mock_success_callback = mocker.MagicMock()
    mock_failure_callback = mocker.MagicMock()

    co.call_api(mock_api_call, mock_success_callback, mock_failure_callback, "foo", bar="baz")

    assert len(co.api_threads) == 1
    thread_info = co.api_threads[list(co.api_threads.keys())[0]]
    thread = thread_info["thread"]
    runner = thread_info["runner"]
    thread.started.connect.assert_called_once_with(runner.call_api)
    thread.start.assert_called_once_with()
    runner.moveToThread.assert_called_once_with(thread)
    assert runner.call_succeeded.connect.call_count == 1
    assert runner.call_failed.connect.call_count == 1
    assert runner.call_timed_out.connect.call_count == 0


def test_Controller_login(homedir, config, mocker, session_maker):
    """
    Ensures the API is called in the expected manner for logging in the user
    given the username, password and 2fa token.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_api = mocker.patch("securedrop_client.logic.sdclientapi.API")
    fail_draft_replies = mocker.patch("securedrop_client.storage.mark_all_pending_drafts_as_failed")

    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.call_api = mocker.MagicMock()
    co.show_last_sync_timer = mocker.MagicMock()

    co.login("username", "password", "123456")

    co.call_api.assert_called_once_with(
        mock_api().authenticate, co.on_authenticate_success, co.on_authenticate_failure
    )
    fail_draft_replies.assert_called_once_with(co.session)
    co.show_last_sync_timer.stop.assert_called_once_with()


def test_Controller_login_offline_mode(homedir, config, mocker):
    """
    Ensures user is not authenticated when logging in in offline mode, that the system
    clipboard is cleared, and that the correct windows are subsequently displayed.
    """
    co = Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)
    co.call_api = mocker.MagicMock()
    co.gui = mocker.MagicMock()
    co.gui.show_main_window = mocker.MagicMock()
    co.gui.hide_login = mocker.MagicMock()
    co.update_sources = mocker.MagicMock()
    co.show_last_sync_timer = mocker.MagicMock()

    co.login_offline_mode()

    assert co.call_api.called is False
    assert co.is_authenticated is False
    co.gui.assert_has_calls([call.clear_clipboard(), call.show_main_window()])
    co.gui.hide_login.assert_called_once_with()
    co.update_sources.assert_called_once_with()
    co.show_last_sync_timer.start.assert_called_once_with(TIME_BETWEEN_SHOWING_LAST_SYNC_MS)


@pytest.mark.parametrize(
    "exception", [AuthError("oh no"), RequestTimeoutError(), ServerConnectionError(), Exception()]
)
def test_Controller_on_authenticate_failure(homedir, config, mocker, session_maker, exception):
    """
    If there is any problem authenticating, make sure the user receives an
    informative error message.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.api_sync.stop = mocker.MagicMock()
    co.on_authenticate_failure(exception)

    if isinstance(exception, (RequestTimeoutError, ServerConnectionError)):
        error = _(
            "Could not reach the SecureDrop server. Please check your \n"
            "Internet and Tor connection and try again."
        )
    elif isinstance(exception, AuthError):
        error = _(
            "Those credentials didn't work. Please try again, and \n"
            "make sure to use a new two-factor code."
        )
    else:
        error = _("That didn't work. Please check everything and try again.")

    co.api_sync.stop.assert_called_once_with()
    mock_gui.show_login_error.assert_called_once_with(error=error)


def test_Controller_on_authenticate_success(homedir, config, mocker, session_maker, session):
    """
    Ensure upon successfully login that the client:
      * starts the sync
      * starts the job queues
      * clears the clipboard
      * emits the update_authenticated_user signal

    Note: Using the `config` fixture ensure the config is written to disk
    """
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.authenticated_user = factory.User()
    co.api_sync.start = mocker.MagicMock()
    co.api_job_queue.start = mocker.MagicMock()
    co.update_sources = mocker.MagicMock()
    co.session.add(co.authenticated_user)
    co.session.commit()
    co.api = mocker.MagicMock()
    co.api.token_journalist_uuid = co.authenticated_user.uuid
    co.api.username = co.authenticated_user.username
    co.api.first_name = co.authenticated_user.firstname
    co.api.last_name = co.authenticated_user.lastname
    co.resume_queues = mocker.MagicMock()
    update_authenticated_user_emissions = QSignalSpy(co.update_authenticated_user)

    co.on_authenticate_success(True)

    co.gui.assert_has_calls([call.clear_clipboard(), call.show_main_window(co.authenticated_user)])
    co.api_sync.start.assert_called_once_with(co.api)
    co.api_job_queue.start.assert_called_once_with(co.api)
    assert co.is_authenticated
    assert len(update_authenticated_user_emissions) == 1
    assert update_authenticated_user_emissions[0] == [co.authenticated_user]


def test_Controller_completed_api_call_without_current_object(
    homedir, config, mocker, session_maker
):
    """
    Ensure that cleanup is performed if an API call returns in the expected
    time.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)

    result = "result"

    mock_thread = mocker.MagicMock()
    mock_runner = mocker.MagicMock()
    mock_runner.result = result
    mock_runner.current_object = None
    co.api_threads = {"thread_uuid": {"thread": mock_thread, "runner": mock_runner}}
    mock_user_callback = mocker.MagicMock()

    co.completed_api_call("thread_uuid", mock_user_callback)

    mock_user_callback.assert_called_once_with(result)


def test_Controller_completed_api_call_with_current_object(homedir, config, mocker, session_maker):
    """
    Ensure that cleanup is performed if an API call returns in the expected
    time.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)

    result = "result"
    current_object = "current_object"

    mock_thread = mocker.MagicMock()
    mock_runner = mocker.MagicMock()
    mock_runner.result = result
    mock_runner.current_object = current_object
    co.api_threads = {"thread_uuid": {"thread": mock_thread, "runner": mock_runner}}
    mock_user_callback = mocker.MagicMock()

    mock_arg_spec = mocker.MagicMock(args=["foo", "current_object"])
    mocker.patch("securedrop_client.logic.inspect.getfullargspec", return_value=mock_arg_spec)

    co.completed_api_call("thread_uuid", mock_user_callback)
    mock_user_callback.assert_called_once_with(result, current_object=current_object)


def test_Controller_on_action_requiring_login(homedir, config, mocker, session_maker):
    """
    Ensure that when on_action_requiring_login is called, an error
    is shown in the GUI status area.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)

    co.on_action_requiring_login()

    mock_gui.update_error_status.assert_called_once_with("You must sign in to perform this action.")


def test_Controller_authenticated_yes(homedir, config, mocker, session_maker):
    """
    If the API is authenticated return True.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.api = mocker.MagicMock()
    co.api.token = "foo"

    assert co.authenticated() is True


def test_Controller_authenticated_no(homedir, config, mocker, session_maker):
    """
    If the API is authenticated return True.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)

    co.api = mocker.MagicMock()
    co.api.token = None

    assert co.authenticated() is False


def test_Controller_authenticated_no_api(homedir, config, mocker, session_maker):
    """
    If the API is authenticated return True.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.api = None

    assert co.authenticated() is False


def test_Controller_last_sync_with_file(homedir, config, mocker, session_maker):
    """
    The flag indicating the time of the last sync with the API is stored in a
    dotfile in the user's home directory. If such a file exists, ensure an
    "arrow" object (representing the date/time) is returned.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)

    timestamp = "2018-10-10 18:17:13+01:00"
    mocker.patch("builtins.open", mocker.mock_open(read_data=timestamp))

    result = co.get_last_sync()

    assert isinstance(result, arrow.Arrow)
    assert result.format() == timestamp


def test_Controller_last_sync_no_file(homedir, config, mocker, session_maker):
    """
    If there's no sync file, then just return None.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)

    mocker.patch("builtins.open", mocker.MagicMock(side_effect=Exception()))
    assert co.get_last_sync() is None


def test_Controller_on_sync_started(mocker, homedir):
    co = Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)

    co.on_sync_started()

    sync_started_emissions = QSignalSpy(co.sync_started)

    co.on_sync_started()

    assert len(sync_started_emissions) == 1


def test_Controller_on_sync_failure(homedir, config, mocker, session_maker):
    """
    If there's no result to syncing, then don't attempt to update local storage
    and perhaps implement some as-yet-undefined UI update.
    Using the `config` fixture to ensure the config is written to disk.
    """
    gui = mocker.MagicMock()
    co = Controller("http://localhost", gui, session_maker, homedir, None)
    co.resume_queues = mocker.MagicMock()
    exception = Exception("mock")  # Not the expected tuple.
    mock_storage = mocker.patch("securedrop_client.logic.storage")

    co.on_sync_failure(exception)

    assert mock_storage.update_local_storage.call_count == 0


def test_Controller_on_sync_failure_due_to_invalid_token(homedir, config, mocker, session_maker):
    """
    If the sync fails because the api is inaccessible then ensure user is logged out and shown the
    login window.
    """
    gui = mocker.MagicMock()
    co = Controller("http://localhost", gui, session_maker, homedir, None)
    co.is_authenticated = True
    co.api = "mock"
    co.logout = mocker.MagicMock()
    co.gui = mocker.MagicMock()
    co.gui.show_login = mocker.MagicMock()
    mock_storage = mocker.patch("securedrop_client.logic.storage")

    co.on_sync_failure(ApiInaccessibleError())

    assert mock_storage.update_local_storage.call_count == 0
    co.logout.assert_called_once_with()
    co.gui.show_login.assert_called_once_with(error="Your session expired. Please log in again.")


def test_Controller_on_sync_failure_due_to_invalid_token_after_user_logs_out(
    homedir, config, mocker, session_maker
):
    """
    If the sync fails because the api is inaccessible but the user is already logged out, do not
    show the login window.
    """
    gui = mocker.MagicMock()
    co = Controller("http://localhost", gui, session_maker, homedir, None)
    co.logout = mocker.MagicMock()
    co.gui = mocker.MagicMock()
    co.gui.show_login = mocker.MagicMock()
    mock_storage = mocker.patch("securedrop_client.logic.storage")

    co.is_authenticated = True
    co.api = None
    co.on_sync_failure(ApiInaccessibleError())
    assert mock_storage.update_local_storage.call_count == 0
    co.logout.assert_not_called()
    co.gui.show_login.assert_not_called()

    co.is_authenticated = False
    co.api = "mock"
    co.on_sync_failure(ApiInaccessibleError())
    assert mock_storage.update_local_storage.call_count == 0
    co.logout.assert_not_called()
    co.gui.show_login.assert_not_called()


@pytest.mark.parametrize("exception", [RequestTimeoutError, ServerConnectionError])
def test_Controller_on_sync_failure_due_to_timeout(homedir, mocker, exception):
    """
    If the sync fails because of a timeout, make sure to show an error message.
    """
    gui = mocker.MagicMock()
    co = Controller("http://localhost", gui, mocker.MagicMock(), homedir, None)
    co.logout = mocker.MagicMock()
    co.gui = mocker.MagicMock()
    co.gui.update_error_status = mocker.MagicMock()

    co.on_sync_failure(exception())

    co.gui.update_error_status.assert_called_once_with(
        "The SecureDrop server cannot be reached. Trying to reconnect...", duration=0
    )


def test_Controller_on_sync_success(homedir, config, mocker):
    """
    If there's a result to syncing, then update local storage.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock(return_value=mock_session)

    co = Controller("http://localhost", mock_gui, mock_session_maker, homedir, None)
    co.authenticated_user = factory.User()
    co.update_sources = mocker.MagicMock()
    co.download_new_messages = mocker.MagicMock()
    co.download_new_replies = mocker.MagicMock()
    co.gpg = mocker.MagicMock()
    co.resume_queues = mocker.MagicMock()
    file_missing_emissions = QSignalSpy(co.file_missing)
    mock_storage = mocker.patch("securedrop_client.logic.storage")
    source = factory.Source()
    missing = factory.File(is_downloaded=None, is_decrypted=None, source=source)
    mock_storage.update_missing_files.return_value = [missing]

    co.on_sync_success()

    mock_storage.update_missing_files.assert_called_once_with(co.data_dir, co.session)
    co.update_sources.assert_called_once_with()
    co.download_new_messages.assert_called_once_with()
    co.download_new_replies.assert_called_once_with()
    co.resume_queues.assert_called_once_with()
    assert len(file_missing_emissions) == 1
    assert file_missing_emissions[0] == [missing.source.uuid, missing.uuid, str(missing)]


def test_Controller_on_sync_success_when_current_user_deleted(mocker, homedir):
    co = Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)

    class DeletedUser(db.User):
        @property
        def username(self):
            raise sqlalchemy.orm.exc.ObjectDeletedError(attributes.instance_state(db.User()), None)

    co.authenticated_user = DeletedUser()
    co.api = "not None"
    co.gui = mocker.MagicMock()

    co.on_sync_success()

    assert co.authenticated_user is None
    assert co.api is None
    assert co.is_authenticated is False
    co.gui.logout.assert_called_once_with()


def test_Controller__close_client_session(mocker, homedir):
    co = Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)
    co.authenticated_user = factory.User(username="foo")
    co.api = "not None"
    co.gui = mocker.MagicMock()

    co._close_client_session()

    assert co.authenticated_user is None
    assert co.api is None
    assert co.is_authenticated is False
    co.gui.logout.assert_called_once_with()
    co.gui.show_login.assert_called_once_with(error="Your session expired. Please log in again.")


def test_Controller_on_sync_success_username_change(homedir, session, config, mocker):
    """
    If there's a result to syncing, then update local storage.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller("http://localhost", mock_gui, mocker.MagicMock(), homedir, None)
    user = factory.User(uuid="abc123", username="foo")
    co.authenticated_user = user
    co.api = mocker.MagicMock(
        username="imdifferent", first_name=user.firstname, last_name=user.lastname
    )
    update_authenticated_user_emissions = QSignalSpy(co.update_authenticated_user)

    co.on_sync_success()

    co.authenticated_user.username == "baz"
    assert len(update_authenticated_user_emissions) == 1
    assert update_authenticated_user_emissions[0] == [co.authenticated_user]


def test_Controller_on_sync_success_firstname_change(homedir, session, config, mocker):
    """
    If there's a result to syncing, then update local storage.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller("http://localhost", mock_gui, mocker.MagicMock(), homedir, None)
    user = factory.User(uuid="abc123", firstname="foo")
    co.authenticated_user = user
    co.api = mocker.MagicMock(
        username=user.username, first_name="imdifferent", last_name=user.lastname
    )
    update_authenticated_user_emissions = QSignalSpy(co.update_authenticated_user)

    co.on_sync_success()

    co.authenticated_user.firstname == "baz"
    assert len(update_authenticated_user_emissions) == 1
    assert update_authenticated_user_emissions[0] == [co.authenticated_user]


def test_Controller_on_sync_success_lastname_change(homedir, session, config, mocker):
    """
    If there's a result to syncing, then update local storage.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()

    co = Controller("http://localhost", mock_gui, mocker.MagicMock(), homedir, None)
    user = factory.User(uuid="abc123", lastname="foo")
    co.authenticated_user = user
    co.api = mocker.MagicMock(
        username=user.username, first_name=user.firstname, last_name="imdifferent"
    )
    update_authenticated_user_emissions = QSignalSpy(co.update_authenticated_user)

    co.on_sync_success()

    co.authenticated_user.lastname == "baz"
    assert len(update_authenticated_user_emissions) == 1
    assert update_authenticated_user_emissions[0] == [co.authenticated_user]


def test_Controller_show_last_sync(homedir, config, mocker, session_maker):
    """
    Ensure we get the last sync time when we show it.
    Using the `config` fixture to ensure the config is written to disk.
    This should only happen if the user isn't logged in or the API queues are
    paused (indicating network problems).
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.get_last_sync = mocker.MagicMock()
    co.api = None

    co.show_last_sync()

    assert co.get_last_sync.call_count == 1
    co.gui.show_last_sync.assert_called_once_with(co.get_last_sync())


def test_Controller_update_sources(homedir, config, mocker):
    """
    Ensure the UI displays a list of the available sources from local data
    store.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock(return_value=mock_session)

    co = Controller("http://localhost", mock_gui, mock_session_maker, homedir, None)

    mock_storage = mocker.patch("securedrop_client.logic.storage")
    source_list = [factory.Source(last_updated=1), factory.Source(last_updated=2)]
    mock_storage.get_local_sources.return_value = source_list

    co.update_sources()

    mock_storage.get_local_sources.assert_called_once_with(mock_session)
    mock_gui.show_sources.assert_called_once_with(source_list)


def test_Controller_mark_seen(homedir, config, mocker, session, session_maker):
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.authenticated_user = factory.User()
    add_job_emissions = QSignalSpy(co.add_job)
    source = factory.Source()
    file = factory.File(source=source)
    message = factory.Message(source=source)
    reply = factory.Reply(source=source)
    session.add(file)
    session.add(message)
    session.add(reply)

    job = mocker.MagicMock()
    job.success_signal = mocker.MagicMock()
    job.failure_signal = mocker.MagicMock()
    mocker.patch("securedrop_client.logic.SeenJob", return_value=job)

    co.mark_seen(source)

    assert len(add_job_emissions) == 1
    assert add_job_emissions[0] == [job]
    job.success_signal.connect.assert_called_once_with(co.on_seen_success, type=Qt.QueuedConnection)
    job.failure_signal.connect.assert_called_once_with(co.on_seen_failure, type=Qt.QueuedConnection)


def test_Controller_mark_seen_with_unseen_item_of_each_type(
    homedir, config, mocker, session, session_maker
):
    """
    Ensure that all source conversation items that have not been seen by the current user are marked
    as seen.
    """
    controller = Controller(
        "http://localhost", mocker.MagicMock(), session_maker, homedir, None, None
    )
    controller.authenticated_user = factory.User(id=1)
    source = factory.Source()

    unseen_file = factory.File(source=source)
    unseen_message = factory.Message(source=source)
    unseen_reply = factory.Reply(source=source)

    session.add(unseen_file)
    session.add(unseen_message)
    session.add(unseen_reply)

    seen_file = factory.File(source=source)
    seen_message = factory.Message(source=source)
    seen_reply = factory.Reply(source=source)
    session.add(seen_file)
    session.add(seen_message)
    session.add(seen_reply)

    unseen_file_for_current_user = factory.File(source=source)
    unseen_message_for_current_user = factory.Message(source=source)
    unseen_reply_for_current_user = factory.Reply(source=source)
    session.add(unseen_file_for_current_user)
    session.add(unseen_message_for_current_user)
    session.add(unseen_reply_for_current_user)

    draft_reply_from_current_user = factory.DraftReply(
        source=source, journalist_id=controller.authenticated_user.id
    )
    draft_reply_from_another_user = factory.DraftReply(source=source, journalist_id=666)
    session.add(draft_reply_from_current_user)
    session.add(draft_reply_from_another_user)

    session.commit()

    session.add(db.SeenFile(file_id=seen_file.id, journalist_id=controller.authenticated_user.id))
    session.add(
        db.SeenMessage(message_id=seen_message.id, journalist_id=controller.authenticated_user.id)
    )
    session.add(
        db.SeenReply(reply_id=seen_reply.id, journalist_id=controller.authenticated_user.id)
    )
    session.add(db.SeenFile(file_id=unseen_file_for_current_user.id, journalist_id=666))
    session.add(db.SeenMessage(message_id=unseen_message_for_current_user.id, journalist_id=666))
    session.add(db.SeenReply(reply_id=unseen_reply_for_current_user.id, journalist_id=666))

    session.commit()

    job = mocker.patch("securedrop_client.logic.SeenJob")

    controller.mark_seen(source)

    job.assert_called_once_with(
        [unseen_file.uuid, unseen_file_for_current_user.uuid],
        [unseen_message.uuid, unseen_message_for_current_user.uuid],
        [unseen_reply.uuid, unseen_reply_for_current_user.uuid],
    )


def test_Controller_mark_seen_with_unseen_file_only(
    homedir, config, mocker, session, session_maker
):
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.authenticated_user = factory.User()
    source = factory.Source()
    file = factory.File(source=source, uuid="file-uuid-1")
    session.add(file)

    job = mocker.patch("securedrop_client.logic.SeenJob")

    co.mark_seen(source)

    job.assert_called_once_with(["file-uuid-1"], [], [])


def test_Controller_mark_seen_with_unseen_message_only(
    homedir, config, mocker, session, session_maker
):
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.authenticated_user = factory.User()
    source = factory.Source()
    message = factory.Message(source=source, uuid="msg-uuid-1")
    session.add(message)

    job = mocker.patch("securedrop_client.logic.SeenJob")

    co.mark_seen(source)

    job.assert_called_once_with([], ["msg-uuid-1"], [])


def test_Controller_mark_seen_with_unseen_reply_only(
    homedir, config, mocker, session, session_maker
):
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.authenticated_user = factory.User()
    source = factory.Source()
    reply = factory.Reply(source=source, uuid="reply-uuid-1")
    session.add(reply)

    job = mocker.patch("securedrop_client.logic.SeenJob")

    co.mark_seen(source)

    job.assert_called_once_with([], [], ["reply-uuid-1"])


def test_Controller_mark_seen_skips_if_no_unseen_items(
    homedir, config, mocker, session, session_maker
):
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.authenticated_user = factory.User()
    add_job_emissions = QSignalSpy(co.add_job)

    job = mocker.MagicMock()
    job.success_signal = mocker.MagicMock()
    job.failure_signal = mocker.MagicMock()
    mocker.patch("securedrop_client.logic.SeenJob", return_value=job)

    co.mark_seen(factory.Source())

    assert len(add_job_emissions) == 0
    job.success_signal.connect.assert_not_called()
    job.failure_signal.connect.assert_not_called()


def test_Controller_mark_seen_skips_op_if_user_offline(
    homedir, config, mocker, session, session_maker
):
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.authenticated_user = None
    add_job_emissions = QSignalSpy(co.add_job)
    source = factory.Source()
    file = factory.File(source=source)
    message = factory.Message(source=source)
    reply = factory.Reply(source=factory.Source())
    session.add(file)
    session.add(message)
    session.add(reply)

    job = mocker.MagicMock()
    job.success_signal = mocker.MagicMock()
    job.failure_signal = mocker.MagicMock()
    mocker.patch("securedrop_client.logic.SeenJob", return_value=job)

    co.mark_seen(source)

    assert len(add_job_emissions) == 0
    job.success_signal.connect.assert_not_called()
    job.failure_signal.connect.assert_not_called()


class DeletedFile(Mock):
    def __class__(self):
        return Type(db.File)

    def seen_by(self, journalist_id):
        raise sqlalchemy.exc.InvalidRequestError()


class SourceWithDeletedFile(Mock):
    @property
    def collection(self):
        deleted_file = DeletedFile()
        return [deleted_file]


def test_Controller_mark_seen_does_not_raise_InvalidRequestError_if_item_deleted(
    homedir, config, mocker, session, session_maker
):
    """
    If a source item no longer exists in the local data store, ensure we do not raise an exception.
    """
    mocker.patch("securedrop_client.logic.isinstance", return_value=True)
    debug_logger = mocker.patch("securedrop_client.logic.logger.debug")
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.authenticated_user = factory.User()

    co.mark_seen(SourceWithDeletedFile())

    assert debug_logger.call_count == 1


class DeletedSourceWhenAccessingCollection(Mock):
    @property
    def collection(self):
        raise sqlalchemy.exc.InvalidRequestError()

    @property
    def uuid(self):
        return "DeletedSourceWhenAccessingCollection_uuid"

    @property
    def seen(self):
        return False

    @property
    def last_updated(self):
        return datetime.now()

    @property
    def is_starred(self):
        return True


def test_Controller_mark_seen_does_not_raise_InvalidRequestError_if_source_deleted(
    homedir, config, mocker, session, session_maker
):
    """
    If a source item no longer exists in the local data store, ensure we do not raise an exception.
    """
    debug_logger = mocker.patch("securedrop_client.logic.logger.debug")
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.authenticated_user = factory.User()

    co.mark_seen(DeletedSourceWhenAccessingCollection())

    assert debug_logger.call_count == 1


def test_Controller_on_seen_success(homedir, mocker, session_maker):
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.on_seen_success()


def test_Controller_on_seen_failure(homedir, mocker, session_maker):
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    debug_logger = mocker.patch("securedrop_client.logic.logger.debug")
    error = Exception("errorororr")
    co.on_seen_failure(error)
    debug_logger.assert_called_once_with(error)


def test_Controller_update_star_not_logged_in(homedir, config, mocker, session_maker):
    """
    Ensure that starring/unstarring a source when not logged in calls
    the method that displays an error status in the left sidebar.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    source_db_object = mocker.MagicMock()
    mock_callback = mocker.MagicMock()
    co.on_action_requiring_login = mocker.MagicMock()
    co.api = None
    co.update_star(source_db_object, mock_callback)
    co.on_action_requiring_login.assert_called_with()


def test_Controller_on_update_star_success(homedir, config, mocker, session_maker):
    """
    If the starring occurs successfully, then a sync should occur to update
    locally.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.star_update_failed = mocker.MagicMock()

    co.on_update_star_success("mock_uuid")


def test_Controller_on_update_star_failed(homedir, config, mocker):
    """
    Check that if starring fails then the failure signal is emitted and the error bar is updated
    with a failure message.
    """
    gui = mocker.MagicMock()
    co = Controller("http://localhost", gui, mocker.MagicMock(), homedir, None)
    star_update_failed_emissions = QSignalSpy(co.star_update_failed)
    source = factory.Source()
    co.session.query().filter_by().one.return_value = source

    error = UpdateStarJobError("mock_message", source.uuid)
    co.on_update_star_failure(error)

    assert len(star_update_failed_emissions) == 1
    assert star_update_failed_emissions[0] == [source.uuid, source.is_starred]
    gui.update_error_status.assert_called_once_with("Failed to update star.")


def test_Controller_on_update_star_failed_due_to_timeout(homedir, config, mocker):
    """
    Ensure the failure signal is not emitted and the error bar is not updated if the star fails due
    to a timeout (regression test).
    """
    gui = mocker.MagicMock()
    co = Controller("http://localhost", gui, mocker.MagicMock(), homedir, None)
    star_update_failed_emissions = QSignalSpy(co.star_update_failed)

    error = UpdateStarJobTimeoutError("mock_message", "mock_uuid")
    co.on_update_star_failure(error)

    assert len(star_update_failed_emissions) == 0
    gui.update_error_status.assert_not_called()


def test_Controller_invalidate_token(mocker, homedir, session_maker):
    """
    Ensure the controller's api token is set to None.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.api = "not None"

    co.invalidate_token()

    assert co.api is None


def test_Controller_logout_with_pending_replies(mocker, session_maker, homedir, reply_status_codes):
    """
    Ensure draft reply fails on logout and that the reply_failed signal is emitted.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.api_job_queue = mocker.MagicMock()
    co.api_job_queue.stop = mocker.MagicMock()
    co.call_api = mocker.MagicMock()
    reply_failed_emissions = QSignalSpy(co.reply_failed)

    source = factory.Source()
    session = session_maker()
    pending_status = (
        session.query(db.ReplySendStatus)
        .filter_by(name=db.ReplySendStatusCodes.PENDING.value)
        .one()
    )
    failed_status = (
        session.query(db.ReplySendStatus).filter_by(name=db.ReplySendStatusCodes.FAILED.value).one()
    )
    pending_draft_reply = factory.DraftReply(source=source, send_status=pending_status)
    session.add(source)
    session.add(pending_draft_reply)

    co.logout()

    for draft in session.query(db.DraftReply).all():
        assert draft.send_status == failed_status

    assert len(reply_failed_emissions) == 1
    assert reply_failed_emissions[0] == [pending_draft_reply.uuid]
    co.api_job_queue.stop.assert_called_once_with()


def test_Controller_logout_with_no_api(homedir, config, mocker, session_maker):
    """
    Ensure we don't attempt to make an api call to logout when the api has been set to None
    because token is invalid.
    """
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.api = None
    co.authenticated_user = factory.User()
    co.api_job_queue = mocker.MagicMock()
    co.api_job_queue.stop = mocker.MagicMock()
    co.call_api = mocker.MagicMock()
    fail_draft_replies = mocker.patch("securedrop_client.storage.mark_all_pending_drafts_as_failed")

    co.logout()

    assert not co.authenticated_user
    co.call_api.assert_not_called()
    co.api_job_queue.stop.assert_called_once_with()
    co.gui.logout.assert_called_once_with()
    fail_draft_replies.called_once_with(co.session)


def test_Controller_logout_success(homedir, config, mocker, session_maker):
    """
    Ensure the API is called on logout and if the API call succeeds,
    the API object is reset to None and the UI is set to logged out state.
    The message and reply threads should also have been reset.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.api = mocker.MagicMock()
    co.api_job_queue = mocker.MagicMock()
    co.api_job_queue.stop = mocker.MagicMock()
    co.call_api = mocker.MagicMock()
    co.show_last_sync_timer = mocker.MagicMock()
    info_logger = mocker.patch("securedrop_client.logic.logging.info")
    fail_draft_replies = mocker.patch("securedrop_client.storage.mark_all_pending_drafts_as_failed")
    logout_method = co.api.logout
    co.logout()
    co.call_api.assert_called_with(logout_method, co.on_logout_success, co.on_logout_failure)
    co.on_logout_success(True)
    assert co.api is None
    co.api_job_queue.stop.assert_called_once_with()
    co.gui.logout.assert_called_once_with()
    msg = "Client logout successful"
    info_logger.assert_called_once_with(msg)
    fail_draft_replies.called_once_with(co.session)
    co.show_last_sync_timer.start.assert_called_once_with(TIME_BETWEEN_SHOWING_LAST_SYNC_MS)


def test_Controller_logout_failure(homedir, config, mocker, session_maker):
    """
    Ensure the API is called on logout and if the API call fails,
    the API object is reset to None and the UI is set to logged out state.
    The message and reply threads should also have been reset.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.api = mocker.MagicMock()
    co.api_job_queue = mocker.MagicMock()
    co.api_job_queue.stop = mocker.MagicMock()
    co.call_api = mocker.MagicMock()
    info_logger = mocker.patch("securedrop_client.logic.logging.info")
    fail_draft_replies = mocker.patch("securedrop_client.storage.mark_all_pending_drafts_as_failed")
    logout_method = co.api.logout

    co.logout()

    co.call_api.assert_called_with(logout_method, co.on_logout_success, co.on_logout_failure)
    co.on_logout_failure(Exception())
    assert co.api is None
    co.api_job_queue.stop.assert_called_once_with()
    co.gui.logout.assert_called_once_with()
    msg = "Client logout failure"
    info_logger.assert_called_once_with(msg)
    fail_draft_replies.called_once_with(co.session)


def test_Controller_set_activity_status(homedir, config, mocker, session_maker):
    """
    Ensure the GUI set_status API is called.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.set_status("Hello, World!", 1000)
    mock_gui.update_activity_status.assert_called_once_with("Hello, World!", 1000)


def test_create_client_dir_permissions(tmpdir, mocker, session_maker):
    """
    Check that creating an app behaves appropriately with different
    permissions on the various directories needed for it to function.
    """
    mock_gui = mocker.MagicMock()

    # we can't rely on the config fixture, and because of the order of exectution,
    # we can't create the config at the right time, we we have to mock both
    # `open` and `json.loads`
    mock_open = mocker.patch("securedrop_client.config.open")
    mock_json = mocker.patch("securedrop_client.config.json.loads")

    permission_cases = [
        {"should_pass": True, "home_perms": None},
        {"should_pass": True, "home_perms": 0o0700},
        {"should_pass": False, "home_perms": 0o0740},
        {"should_pass": False, "home_perms": 0o0704},
    ]

    for idx, case in enumerate(permission_cases):
        sdc_home = os.path.join(str(tmpdir), "case-{}".format(idx))

        # optionally create the dir
        if case["home_perms"] is not None:
            os.mkdir(sdc_home)
            os.chmod(sdc_home, case["home_perms"])

        def func() -> None:
            Controller("http://localhost", mock_gui, session_maker, sdc_home, None)

        if case["should_pass"]:
            func()
        else:
            with pytest.raises(RuntimeError):
                func()

    # check that both mocks were called to ensure they aren't "dead code"
    assert mock_open.called
    assert mock_json.called


def test_Controller_download_conversation(homedir, config, session, mocker, session_maker):

    app_state = state.State()
    gui = mocker.MagicMock()
    co = Controller("http://localhost", gui, session_maker, homedir, app_state)
    co.api = "journalist is authenticated"

    add_job_emissions = QSignalSpy(co.add_job)
    file_download_started_emissions = QSignalSpy(co.file_download_started)

    job_success_signal = mocker.MagicMock()
    job_failure_signal = mocker.MagicMock()
    job = mocker.MagicMock(success_signal=job_success_signal, failure_signal=job_failure_signal)
    file_download_job_constructor = mocker.patch(
        "securedrop_client.logic.FileDownloadJob", return_value=job
    )

    conversation_id = state.ConversationId("some_conversation")
    unrelated_conversation_id = state.ConversationId("unrelated_conversation")
    some_file_id = state.FileId("some_file")
    another_file_id = state.FileId("another_file")
    unrelated_file_id = state.FileId("unrelated_file")

    app_state.add_file(conversation_id, some_file_id)
    app_state.add_file(conversation_id, another_file_id)
    app_state.add_file(unrelated_conversation_id, unrelated_file_id)

    co.download_conversation(conversation_id)

    expected = [
        call(some_file_id, co.data_dir, co.gpg),
        call(another_file_id, co.data_dir, co.gpg),
    ]
    assert file_download_job_constructor.mock_calls == expected

    assert len(add_job_emissions) == 2
    assert add_job_emissions[0] == [job]
    assert add_job_emissions[1] == [job]
    expected = [
        call(co.on_file_download_success, type=Qt.QueuedConnection),
        call(co.on_file_download_success, type=Qt.QueuedConnection),
    ]
    assert job_success_signal.connect.mock_calls == expected
    expected = [
        call(co.on_file_download_failure, type=Qt.QueuedConnection),
        call(co.on_file_download_failure, type=Qt.QueuedConnection),
    ]
    assert job_failure_signal.connect.mock_calls == expected

    assert len(file_download_started_emissions) == 2
    assert file_download_started_emissions[0] == [some_file_id]
    assert file_download_started_emissions[1] == [another_file_id]


def test_Controller_download_conversation_requires_authenticated_journalist(
    homedir, config, session, mocker, session_maker
):
    app_state = state.State()
    gui = mocker.MagicMock()
    co = Controller("http://localhost", gui, session_maker, homedir, app_state)
    co.api = None  # journalist is not authenticated

    add_job_emissions = QSignalSpy(co.add_job)
    file_download_started_emissions = QSignalSpy(co.file_download_started)
    co.on_action_requiring_login = mocker.MagicMock()

    job_success_signal = mocker.MagicMock()
    job_failure_signal = mocker.MagicMock()
    job = mocker.MagicMock(success_signal=job_success_signal, failure_signal=job_failure_signal)
    file_download_job_constructor = mocker.patch(
        "securedrop_client.logic.FileDownloadJob", return_value=job
    )

    conversation_id = state.ConversationId("some_conversation")
    unrelated_conversation_id = state.ConversationId("unrelated_conversation")
    some_file_id = state.FileId("some_file")
    another_file_id = state.FileId("another_file")
    unrelated_file_id = state.FileId("unrelated_file")

    app_state.add_file(conversation_id, some_file_id)
    app_state.add_file(conversation_id, another_file_id)
    app_state.add_file(unrelated_conversation_id, unrelated_file_id)

    co.download_conversation(conversation_id)

    assert not file_download_job_constructor.called
    assert len(add_job_emissions) == 0
    assert not job_success_signal.connect.called
    assert not job_failure_signal.connect.called
    assert len(file_download_started_emissions) == 0
    assert co.on_action_requiring_login.called


def test_Controller_on_file_download_Submission(homedir, config, session, mocker, session_maker):
    """
    If the handler is passed a Submission, check the download_submission
    function is the one called against the API.
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.api = "this has a value"

    mock_success_signal = mocker.MagicMock()
    mock_failure_signal = mocker.MagicMock()
    mock_job = mocker.MagicMock(
        success_signal=mock_success_signal, failure_signal=mock_failure_signal
    )
    mock_job_cls = mocker.patch("securedrop_client.logic.FileDownloadJob", return_value=mock_job)
    add_job_emissions = QSignalSpy(co.add_job)

    source = factory.Source()
    file_ = factory.File(is_downloaded=None, is_decrypted=None, source=source)
    session.add(source)
    session.add(file_)
    session.commit()

    co.on_submission_download(db.File, file_.uuid)

    mock_job_cls.assert_called_once_with(file_.uuid, co.data_dir, co.gpg)
    assert len(add_job_emissions) == 1
    assert add_job_emissions[0] == [mock_job]
    mock_success_signal.connect.assert_called_once_with(
        co.on_file_download_success, type=Qt.QueuedConnection
    )
    mock_failure_signal.connect.assert_called_once_with(
        co.on_file_download_failure, type=Qt.QueuedConnection
    )


def test_Controller_on_file_download_Submission_no_auth(
    homedir, config, session, mocker, session_maker
):
    """If the controller is not authenticated, do not enqueue a download job"""
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.on_action_requiring_login = mocker.MagicMock()
    co.api = None

    mock_success_signal = mocker.MagicMock()
    mock_failure_signal = mocker.MagicMock()
    mock_job = mocker.MagicMock(
        success_signal=mock_success_signal, failure_signal=mock_failure_signal
    )
    mock_job_cls = mocker.patch("securedrop_client.logic.FileDownloadJob", return_value=mock_job)
    add_job_emissions = QSignalSpy(co.add_job)

    source = factory.Source()
    file_ = factory.File(is_downloaded=None, is_decrypted=None, source=source)
    session.add(source)
    session.add(file_)
    session.commit()

    co.on_submission_download(db.File, file_.uuid)

    assert not mock_job_cls.called
    assert len(add_job_emissions) == 0
    assert not mock_success_signal.connect.called
    assert not mock_failure_signal.connect.called
    assert co.on_action_requiring_login.called


def test_Controller_on_file_downloaded_success(homedir, config, mocker, session_maker):
    """
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    app_state = state.State()
    app_state.add_file("any_conversation_id", state.FileId("file_uuid"))

    co = Controller("http://localhost", mock_gui, session_maker, homedir, app_state)
    co.session = mocker.MagicMock()

    file_ready_emissions = QSignalSpy(co.file_ready)

    mock_storage = mocker.MagicMock()
    mock_file = mocker.MagicMock()
    mock_file.filename = "foo.txt"
    mock_file.source.uuid = "a_uuid"
    mock_storage.get_file.return_value = mock_file

    mocker.patch("securedrop_client.logic.storage", mock_storage)

    co.on_file_download_success("file_uuid")

    assert len(file_ready_emissions) == 1
    assert file_ready_emissions[0] == ["a_uuid", "file_uuid", "foo.txt"]


def test_Controller_on_file_downloaded_success_updates_application_state(
    homedir, config, mocker, session_maker
):
    """
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    app_state = state.State()

    co = Controller("http://localhost", mock_gui, session_maker, homedir, app_state)
    co.session = mocker.MagicMock()

    mock_storage = mocker.MagicMock()
    mock_file = mocker.MagicMock()
    mock_file.filename = "foo.txt"
    mock_file.source.uuid = "a_uuid"
    mock_storage.get_file.return_value = mock_file
    mocker.patch("securedrop_client.logic.storage", mock_storage)

    app_state.add_file("a_uuid", state.FileId("file_uuid"))

    assert app_state.file(state.FileId("file_uuid"))
    assert not app_state.file(state.FileId("file_uuid")).is_downloaded

    co.on_file_download_success("file_uuid")

    assert app_state.file(state.FileId("file_uuid")).is_downloaded


def test_Controller_on_file_downloaded_api_failure(homedir, config, mocker, session_maker):
    """
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)

    file_ready_emissions = QSignalSpy(co.file_ready)
    mock_update_error_status = mocker.patch.object(mock_gui, "update_error_status")
    result_data = DownloadException("error message", type(db.File), "test-uuid")

    co.on_file_download_failure(result_data)

    mock_update_error_status.assert_called_once_with("The file download failed. Please try again.")
    assert len(file_ready_emissions) == 0


def test_Controller_on_file_downloaded_checksum_failure(homedir, config, mocker, session_maker):
    """
    Check that a failed download due to checksum resubmits the job and informs the user.
    """

    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)

    file_ = factory.File(is_downloaded=None, is_decrypted=None, source=factory.Source())

    mock_set_status = mocker.patch.object(co, "set_status")
    file_ready_emissions = QSignalSpy(co.file_ready)

    warning_logger = mocker.patch("securedrop_client.logic.logger.warning")
    co._submit_download_job = mocker.MagicMock()

    co.on_file_download_failure(DownloadChecksumMismatchException("bang!", type(file_), file_.uuid))

    assert len(file_ready_emissions) == 0

    # Job should get resubmitted and we should log this is happening
    assert co._submit_download_job.call_count == 1
    warning_logger.call_args_list[0][0][
        0
    ] == "Failure due to checksum mismatch, retrying {}".format(file_.uuid)

    # No status will be set if it's a file corruption issue, the file just gets
    # re-downloaded.
    mock_set_status.assert_not_called()


def test_Controller_on_file_decryption_failure(homedir, config, mocker, session, session_maker):
    """
    Check handling of a download decryption failure.
    """

    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)

    file_ = factory.File(is_downloaded=True, is_decrypted=False, source=factory.Source())
    session.add(file_)
    session.commit()

    mock_set_status = mocker.patch.object(co, "set_status")
    file_ready_emissions = QSignalSpy(co.file_ready)
    mock_update_error_status = mocker.patch.object(mock_gui, "update_error_status")

    error_logger = mocker.patch("securedrop_client.logic.logger.error")
    co._submit_download_job = mocker.MagicMock()

    co.on_file_download_failure(DownloadDecryptionException("bang!", type(file_), file_.uuid))

    assert len(file_ready_emissions) == 0
    mock_update_error_status.assert_called_once_with("The file download failed. Please try again.")

    assert co._submit_download_job.call_count == 0
    error_logger.call_args_list[0][0][0] == "Failed to decrypt {}".format(file_.uuid)

    mock_set_status.assert_not_called()


def test_Controller_on_file_open(homedir, config, mocker, session, session_maker, source):
    """
    If running on Qubes, a new QProcess with the expected command and args should be started when
    the file does not exist.

    Using the `config` fixture to ensure the config is written to disk.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.qubes = True
    file = factory.File(source=source["source"])
    session.add(file)
    session.commit()
    mock_subprocess = mocker.MagicMock()
    mock_process = mocker.MagicMock(return_value=mock_subprocess)
    mocker.patch("securedrop_client.logic.QProcess", mock_process)

    filepath = file.location(co.data_dir)
    os.makedirs(os.path.dirname(filepath))
    with open(filepath, "w"):
        pass

    co.on_file_open(file)

    mock_process.assert_called_once_with(co)
    assert mock_subprocess.start.call_count == 1


def test_Controller_on_file_open_not_qubes(homedir, config, mocker, session, session_maker, source):
    """
    Check that we just check if the file exists if not running on Qubes.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.qubes = False
    file = factory.File(source=source["source"])
    session.add(file)
    session.commit()

    filepath = file.location(co.data_dir)
    os.makedirs(os.path.dirname(filepath))
    with open(filepath, "w"):
        pass

    co.on_file_open(file)


def test_Controller_on_file_open_when_orig_file_already_exists(
    homedir, config, mocker, session, session_maker, source
):
    """
    If running on Qubes, a new QProcess with the expected command and args should be started when
    the path to original_file already exists.

    Using the `config` fixture to ensure the config is written to disk.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.qubes = True
    file = factory.File(source=source["source"])
    session.add(file)
    session.commit()
    mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)
    mock_subprocess = mocker.MagicMock()
    mock_process = mocker.MagicMock(return_value=mock_subprocess)
    mocker.patch("securedrop_client.logic.QProcess", mock_process)

    filepath = file.location(co.data_dir)
    os.makedirs(os.path.dirname(filepath), mode=0o700, exist_ok=True)
    with open(filepath, "w"):
        pass

    co.on_file_open(file)

    mock_process.assert_called_once_with(co)
    assert mock_subprocess.start.call_count == 1


def test_Controller_on_file_open_when_orig_file_already_exists_not_qubes(
    homedir, config, mocker, session, session_maker, source
):
    """
    Check that we just check if the file exists if not running on Qubes.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.qubes = False
    file = factory.File(source=source["source"])
    session.add(file)
    session.commit()
    mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)

    filepath = file.location(co.data_dir)
    os.makedirs(os.path.dirname(filepath), mode=0o700, exist_ok=True)
    with open(filepath, "w"):
        pass

    co.on_file_open(file)


def test_Controller_on_file_open_file_missing(mocker, homedir, session_maker, session, source):
    """
    When file does not exist, test that we log and send status update to user.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    file = factory.File(source=source["source"])
    session.add(file)
    session.commit()
    mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)
    warning_logger = mocker.patch("securedrop_client.logic.logger.warning")

    co.on_file_open(file)

    log_msg = "Cannot find file in {}. File does not exist.".format(os.path.dirname(file.filename))
    warning_logger.assert_called_once_with(log_msg)


def test_Controller_on_file_open_file_missing_not_qubes(
    mocker, homedir, session_maker, session, source
):
    """
    When file does not exist on a non-qubes system, test that we log and send status update to user.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.qubes = False
    file = factory.File(source=source["source"])
    session.add(file)
    session.commit()
    mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)
    warning_logger = mocker.patch("securedrop_client.logic.logger.warning")

    co.on_file_open(file)

    log_msg = "Cannot find file in {}. File does not exist.".format(os.path.dirname(file.filename))
    warning_logger.assert_called_once_with(log_msg)


def test_Controller_download_new_replies_with_new_reply(mocker, session, session_maker, homedir):
    """
    Test that `download_new_replies` enqueues a job, connects to the right slots, and sets a
    user-facing status message when a new reply is found.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.api = "Api token has a value"
    reply = factory.Reply(source=factory.Source())
    mocker.patch("securedrop_client.storage.find_new_replies", return_value=[reply])
    success_signal = mocker.MagicMock()
    failure_signal = mocker.MagicMock()
    job = mocker.MagicMock(success_signal=success_signal, failure_signal=failure_signal)
    mocker.patch("securedrop_client.logic.ReplyDownloadJob", return_value=job)
    add_job_emissions = QSignalSpy(co.add_job)

    co.download_new_replies()

    assert len(add_job_emissions) == 1
    assert add_job_emissions[0] == [job]
    success_signal.connect.assert_called_once_with(
        co.on_reply_download_success, type=Qt.QueuedConnection
    )
    failure_signal.connect.assert_called_once_with(
        co.on_reply_download_failure, type=Qt.QueuedConnection
    )


def test_Controller_download_new_replies_without_replies(mocker, session, session_maker, homedir):
    """
    Test that `download_new_replies` does not enqueue any jobs or connect to slots or set a
    user-facing status message when there are no new replies found.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    mocker.patch("securedrop_client.storage.find_new_replies", return_value=[])
    success_signal = mocker.MagicMock()
    failure_signal = mocker.MagicMock()
    job = mocker.MagicMock(success_signal=success_signal, failure_signal=failure_signal)
    mocker.patch("securedrop_client.logic.ReplyDownloadJob", return_value=job)
    add_job_emissions = QSignalSpy(co.add_job)
    set_status = mocker.patch.object(co, "set_status")

    co.download_new_replies()

    assert len(add_job_emissions) == 0
    success_signal.connect.assert_not_called()
    failure_signal.connect.assert_not_called()
    set_status.assert_not_called()


def test_Controller_on_reply_downloaded_success(mocker, homedir, session_maker):
    """
    Check that a successful download emits proper signal.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    reply_ready_emissions = QSignalSpy(co.reply_ready)
    reply = factory.Reply(source=factory.Source())
    mocker.patch("securedrop_client.storage.get_reply", return_value=reply)

    co.on_reply_download_success(reply.uuid)

    assert len(reply_ready_emissions) == 1
    assert reply_ready_emissions[0] == [reply.source.uuid, reply.uuid, str(reply)]


def test_Controller_on_reply_downloaded_failure(mocker, homedir, session_maker):
    """
    Check that a failed download informs the user.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    reply_ready_emissions = QSignalSpy(co.reply_ready)
    reply = factory.Reply(source=factory.Source())
    mocker.patch("securedrop_client.storage.get_reply", return_value=reply)
    co._submit_download_job = mocker.MagicMock()

    co.on_reply_download_failure(Exception("mock_exception"))

    assert len(reply_ready_emissions) == 0

    # Job should not get automatically resubmitted if the failure was generic
    co._submit_download_job.assert_not_called()


def test_Controller_on_reply_downloaded_checksum_failure(mocker, homedir, session_maker):
    """
    Check that a failed download due to checksum resubmits the job and informs the user.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    reply_ready_emissions = QSignalSpy(co.reply_ready)
    reply = factory.Reply(source=factory.Source())
    mocker.patch("securedrop_client.storage.get_reply", return_value=reply)
    warning_logger = mocker.patch("securedrop_client.logic.logger.warning")
    co._submit_download_job = mocker.MagicMock()

    co.on_reply_download_failure(
        DownloadChecksumMismatchException("bang!", type(reply), reply.uuid)
    )

    assert len(reply_ready_emissions) == 0

    # Job should get resubmitted and we should log this is happening
    assert co._submit_download_job.call_count == 1
    warning_logger.call_args_list[0][0][
        0
    ] == "Failure due to checksum mismatch, retrying {}".format(reply.uuid)


def test_Controller_on_reply_downloaded_decryption_failure(mocker, homedir, session_maker):
    """
    Check that a failed download due to a decryption error informs the user.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    reply_ready_emissions = QSignalSpy(co.reply_ready)
    reply_download_failed_emissions = QSignalSpy(co.reply_download_failed)
    reply = factory.Reply(source=factory.Source())
    mocker.patch("securedrop_client.storage.get_reply", return_value=reply)

    decryption_exception = DownloadDecryptionException("bang!", type(reply), reply.uuid)
    co.on_reply_download_failure(decryption_exception)

    assert len(reply_ready_emissions) == 0
    assert len(reply_download_failed_emissions) == 1
    assert reply_download_failed_emissions[0] == [reply.source.uuid, reply.uuid, str(reply)]


def test_Controller_download_new_messages_with_new_message(mocker, session, session_maker, homedir):
    """
    Test that `download_new_messages` enqueues a job, connects to the right slots, and sets a
    usre-facing status message when a new message is found.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.api = "Api token has a value"
    message = factory.Message(source=factory.Source())
    mocker.patch("securedrop_client.storage.find_new_messages", return_value=[message])
    success_signal = mocker.MagicMock()
    failure_signal = mocker.MagicMock()
    add_job_emissions = QSignalSpy(co.add_job)
    job = mocker.MagicMock(success_signal=success_signal, failure_signal=failure_signal)
    mocker.patch("securedrop_client.logic.MessageDownloadJob", return_value=job)
    set_status = mocker.patch.object(co, "set_status")

    co.download_new_messages()

    assert len(add_job_emissions) == 1
    assert add_job_emissions[0] == [job]
    success_signal.connect.assert_called_once_with(
        co.on_message_download_success, type=Qt.QueuedConnection
    )
    failure_signal.connect.assert_called_once_with(
        co.on_message_download_failure, type=Qt.QueuedConnection
    )
    set_status.assert_called_once_with("Retrieving new messages", 2500)


def test_Controller_download_new_messages_without_messages(mocker, session, session_maker, homedir):
    """
    Test that `download_new_messages` does not enqueue any jobs or connect to slots or set a
    user-facing status message when there are no new messages found.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    mocker.patch("securedrop_client.storage.find_new_messages", return_value=[])
    success_signal = mocker.MagicMock()
    failure_signal = mocker.MagicMock()
    job = mocker.MagicMock(success_signal=success_signal, failure_signal=failure_signal)
    mocker.patch("securedrop_client.logic.MessageDownloadJob", return_value=job)
    add_job_emissions = QSignalSpy(co.add_job)
    set_status = mocker.patch.object(co, "set_status")

    co.download_new_messages()

    assert len(add_job_emissions) == 0
    success_signal.connect.assert_not_called()
    failure_signal.connect.assert_not_called()
    set_status.assert_not_called()


def test_Controller_download_new_messages_skips_recent_failures(
    mocker, session, session_maker, homedir, download_error_codes
):
    """
    Test that `download_new_messages` skips recently failed downloads.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.api = "Api token has a value"
    add_job_emissions = QSignalSpy(co.add_job)

    # record the download failures
    download_error = (
        session.query(db.DownloadError)
        .filter_by(name=db.DownloadErrorCodes.DECRYPTION_ERROR.name)
        .one()
    )

    message = factory.Message(source=factory.Source())
    message.download_error = download_error
    session.commit()

    mocker.patch("securedrop_client.storage.find_new_messages", return_value=[message])
    mocker.patch("securedrop_client.logic.logger.isEnabledFor", return_value=logging.DEBUG)
    info_logger = mocker.patch("securedrop_client.logic.logger.info")

    co.download_new_messages()

    assert len(add_job_emissions) == 0
    info_logger.call_args_list[0][0][0] == (
        f"Download of message {message.uuid} failed since client start; not retrying."
    )


def test_Controller_download_new_replies_skips_recent_failures(
    mocker, session, session_maker, homedir, download_error_codes
):
    """
    Test that `download_new_replies` skips recently failed downloads.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.api = "Api token has a value"
    add_job_emissions = QSignalSpy(co.add_job)

    # record the download failures
    download_error = (
        session.query(db.DownloadError)
        .filter_by(name=db.DownloadErrorCodes.DECRYPTION_ERROR.name)
        .one()
    )

    reply = factory.Reply(source=factory.Source())
    reply.download_error = download_error
    reply.last_updated = datetime.datetime.utcnow()
    session.commit()

    mocker.patch("securedrop_client.storage.find_new_replies", return_value=[reply])
    mocker.patch("securedrop_client.logic.logger.isEnabledFor", return_value=logging.DEBUG)
    info_logger = mocker.patch("securedrop_client.logic.logger.info")

    co.download_new_replies()

    assert len(add_job_emissions) == 0
    info_logger.call_args_list[0][0][0] == (
        f"Download of reply {reply.uuid} failed since client start; not retrying."
    )


def test_Controller_on_message_downloaded_success(mocker, homedir, session_maker):
    """
    Check that a successful download emits proper signal.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    message_ready_emissions = QSignalSpy(co.message_ready)
    message = factory.Message(source=factory.Source())
    mocker.patch("securedrop_client.storage.get_message", return_value=message)

    co.on_message_download_success(message.uuid)

    assert len(message_ready_emissions) == 1
    assert message_ready_emissions[0] == [message.source.uuid, message.uuid, str(message)]


def test_Controller_on_message_downloaded_failure(mocker, homedir, session_maker):
    """
    Check that a failed download informs the user.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    message_ready_emissions = QSignalSpy(co.message_ready)
    message = factory.Message(source=factory.Source())
    mocker.patch("securedrop_client.storage.get_message", return_value=message)
    co._submit_download_job = mocker.MagicMock()

    co.on_message_download_failure(Exception("mock_exception"))

    assert len(message_ready_emissions) == 0

    # Job should not get automatically resubmitted if the failure was generic
    co._submit_download_job.assert_not_called()


def test_Controller_on_message_downloaded_checksum_failure(mocker, homedir, session_maker):
    """
    Check that a failed download due to checksum resubmits the job and informs the user.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    message_ready_emissions = QSignalSpy(co.message_ready)
    message = factory.Message(source=factory.Source())
    mocker.patch("securedrop_client.storage.get_message", return_value=message)
    co._submit_download_job = mocker.MagicMock()

    co.on_message_download_failure(
        DownloadChecksumMismatchException("bang!", type(message), message.uuid)
    )
    assert len(message_ready_emissions) == 0

    # Job should get resubmitted and we should log this is happening
    assert co._submit_download_job.call_count == 1


def test_Controller_on_message_downloaded_decryption_failure(mocker, homedir, session_maker):
    """
    Check that a failed download due to a decryption error informs the user.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    message_ready_emissions = QSignalSpy(co.message_ready)
    message_download_failed_emissions = QSignalSpy(co.message_download_failed)
    message = factory.Message(source=factory.Source())
    mocker.patch("securedrop_client.storage.get_message", return_value=message)

    decryption_exception = DownloadDecryptionException("bang!", type(message), message.uuid)
    co.on_message_download_failure(decryption_exception)

    assert len(message_ready_emissions) == 0
    assert len(message_download_failed_emissions) == 1
    assert message_download_failed_emissions[0] == [message.source.uuid, message.uuid, str(message)]


def test_Controller_on_delete_source_success(mocker, homedir, session_maker):
    """
    Test that on a successful deletion callback, controller deletes the source from local storage.
    """
    co = Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)
    co.source_deleted = mocker.MagicMock()
    storage = mocker.patch("securedrop_client.logic.storage")

    co.on_delete_source_success("uuid")

    storage.delete_local_source_by_uuid.assert_called_once_with(co.session, "uuid", co.data_dir)


def test_Controller_on_delete_source_failure(homedir, config, mocker, session_maker):
    """
    Using the `config` fixture to ensure the config is written to disk.
    """
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.on_delete_source_failure(DeleteSourceJobException("weow", "uuid"))
    co.gui.update_error_status.assert_called_with("Failed to delete source at server")


def test_Controller_delete_source_not_logged_in(homedir, config, mocker, session_maker):
    """
    Deleting a source when not logged in should cause an error.

    Ensure that trying to delete a source when not logged in calls the
    method that displays an error status in the left sidebar.
    """
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    source_db_object = mocker.MagicMock()
    co.on_action_requiring_login = mocker.MagicMock()
    co.api = None
    co.delete_source(source_db_object)
    co.on_action_requiring_login.assert_called_with()


def test_Controller_delete_source(homedir, config, mocker, session_maker, session):
    """
    Check that a DeleteSourceJob is submitted when delete_source is called.
    """
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.call_api = mocker.MagicMock()
    co.api = mocker.MagicMock()
    add_job_emissions = QSignalSpy(co.add_job)
    source_deleted_emissions = QSignalSpy(co.source_deleted)

    mock_success_signal = mocker.MagicMock()
    mock_failure_signal = mocker.MagicMock()
    mock_job = mocker.MagicMock(
        success_signal=mock_success_signal, failure_signal=mock_failure_signal
    )
    mock_job_cls = mocker.patch("securedrop_client.logic.DeleteSourceJob", return_value=mock_job)

    source = factory.Source()
    session.add(source)
    session.commit()

    co.delete_source(source)

    assert len(source_deleted_emissions) == 1
    assert source_deleted_emissions[0] == [source.uuid]
    mock_job_cls.assert_called_once_with(source.uuid)
    assert len(add_job_emissions) == 1
    assert add_job_emissions[0] == [mock_job]
    mock_success_signal.connect.assert_called_once_with(
        co.on_delete_source_success, type=Qt.QueuedConnection
    )
    mock_failure_signal.connect.assert_called_once_with(
        co.on_delete_source_failure, type=Qt.QueuedConnection
    )


def test_Controller_on_delete_conversation_success(mocker, homedir):
    mocker.patch("securedrop_client.logic.logger.isEnabledFor", return_value=logging.DEBUG)
    info_logger = mocker.patch("securedrop_client.logic.logger.info")

    co = Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)
    mock_storage = mocker.MagicMock()
    mocker.patch("securedrop_client.logic.storage", mock_storage)

    co.on_delete_conversation_success("uuid-blah")

    info_logger.assert_called_once_with(
        "Conversation %s successfully scheduled for deletion at server", "uuid-blah"
    )
    mock_storage.delete_local_conversation_by_source_uuid.assert_called_once_with(
        co.session, "uuid-blah", co.data_dir
    )


def test_Controller_on_delete_conversation_failure(homedir, config, mocker, session_maker, session):
    mock_gui = mocker.MagicMock()
    debug_logger = mocker.patch("securedrop_client.logic.logger.debug")

    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.on_delete_conversation_failure(DeleteConversationJobException("weow", "uuid"))
    debug_logger.assert_called_once_with("Failed to delete conversation %s at server", "uuid")
    co.gui.update_error_status.assert_called_with("Failed to delete conversation at server")


def test_Controller_delete_conversation_not_logged_in(homedir, config, mocker, session_maker):
    """
    Deleting a conversation when not logged in should cause an error.
    """
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    source_db_object = mocker.MagicMock()
    co.on_action_requiring_login = mocker.MagicMock()
    co.api = None
    co.delete_conversation(source_db_object)
    co.on_action_requiring_login.assert_called_with()


def test_Controller_delete_conversation(homedir, config, mocker, session_maker, session):
    """
    Check that a DeleteConversationJob is submitted when delete_conversation is called.
    """
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.call_api = mocker.MagicMock()
    co.api = mocker.MagicMock()
    conversation_deleted_emissions = QSignalSpy(co.conversation_deleted)
    add_job_emissions = QSignalSpy(co.add_job)

    mock_success_signal = mocker.MagicMock()
    mock_failure_signal = mocker.MagicMock()
    mock_job = mocker.MagicMock(
        success_signal=mock_success_signal, failure_signal=mock_failure_signal
    )
    mock_job_cls = mocker.patch(
        "securedrop_client.logic.DeleteConversationJob", return_value=mock_job
    )

    source = factory.Source()
    session.add(source)
    session.commit()

    co.delete_conversation(source)

    assert len(conversation_deleted_emissions) == 1
    assert conversation_deleted_emissions[0] == [source.uuid]
    mock_job_cls.assert_called_once_with(source.uuid)
    assert len(add_job_emissions) == 1
    assert add_job_emissions[0] == [mock_job]
    mock_success_signal.connect.assert_called_once_with(
        co.on_delete_conversation_success, type=Qt.QueuedConnection
    )
    mock_failure_signal.connect.assert_called_once_with(
        co.on_delete_conversation_failure, type=Qt.QueuedConnection
    )


def test_Controller_send_reply_success(
    homedir, config, mocker, session_maker, session, reply_status_codes
):
    """
    Check that a SendReplyJob is submitted to the queue when send_reply is called.
    """
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.authenticated_user = factory.User()
    co.api = mocker.MagicMock()
    co.api.token_journalist_uuid = co.authenticated_user.uuid
    user = factory.User(uuid=co.authenticated_user.uuid)
    session.add(user)
    session.commit()

    mock_success_signal = mocker.MagicMock()
    mock_failure_signal = mocker.MagicMock()
    mock_job = mocker.MagicMock(
        success_signal=mock_success_signal, failure_signal=mock_failure_signal
    )
    mock_job_cls = mocker.patch("securedrop_client.logic.SendReplyJob", return_value=mock_job)
    add_job_emissions = QSignalSpy(co.add_job)

    source = factory.Source()
    session.add(source)
    session.commit()

    co.send_reply(source.uuid, user.uuid, "mock_msg")

    mock_job_cls.assert_called_once_with(source.uuid, user.uuid, "mock_msg", co.gpg)

    assert len(add_job_emissions) == 1
    assert add_job_emissions[0] == [mock_job]
    mock_success_signal.connect.assert_called_once_with(
        co.on_reply_success, type=Qt.QueuedConnection
    )
    mock_failure_signal.connect.assert_called_once_with(
        co.on_reply_failure, type=Qt.QueuedConnection
    )


def test_Controller_send_reply_does_not_send_if_not_authenticated(
    homedir, mocker, session_maker, session
):
    """
    Check that when the user is not authenticated, the failure signal is emitted.
    """
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.api = None

    mock_job_cls = mocker.patch("securedrop_client.logic.SendReplyJob")

    source = factory.Source()
    session.add(source)
    session.commit()

    co.send_reply(source.uuid, "mock_reply_uuid", "mock_msg")

    mock_job_cls.assert_not_called()


def test_Controller_send_reply_does_not_send_if_no_user_account(
    homedir, mocker, session_maker, session
):
    """
    Check that when the user is not authenticated, the failure signal is emitted.
    """
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.api = mocker.MagicMock()
    co.authenticated_user = None

    mock_job_cls = mocker.patch("securedrop_client.logic.SendReplyJob")

    source = factory.Source()
    session.add(source)
    session.commit()

    co.send_reply(source.uuid, "mock_reply_uuid", "mock_msg")

    mock_job_cls.assert_not_called()


def test_Controller_send_reply_handles_deleted_source(homedir, mocker, session_maker, session):
    """
    Check that when a source is deleted by another thread, a reply to the
    source is not sent and the error is logged.
    """

    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.api = mocker.MagicMock()
    co.authenticated_user = mocker.MagicMock()

    source = factory.Source()
    session.add(source)
    session.commit()

    mock_job_cls = mocker.patch("securedrop_client.logic.SendReplyJob")
    mock_error = mocker.patch("securedrop_client.logic.logger.error")
    mock_update = mocker.patch("securedrop_client.logic.Controller.update_sources")

    # Simulate source being deleted in another thread
    session.delete(source)
    session.commit()

    co.send_reply(source.uuid, "mock_reply_uuid", "mock_msg")

    mock_job_cls.assert_not_called()
    mock_error.assert_called_once_with(
        "Cannot send a reply to a source account that has been deleted"
    )
    mock_update.assert_called()


def test_Controller_on_reply_success(homedir, mocker, session_maker, session):
    """
    Check that when the method is called, the client emits the correct signal.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    reply_succeeded_emissions = QSignalSpy(co.reply_succeeded)
    reply_failed_emissions = QSignalSpy(co.reply_failed)
    reply = factory.Reply(source=factory.Source())
    info_logger = mocker.patch("securedrop_client.logic.logger.info")

    mock_storage = mocker.MagicMock()
    mock_reply = mocker.MagicMock()
    mock_reply.content = "reply_message_mock"
    mock_reply.source.uuid = "source_uuid"
    mock_storage.get_reply.return_value = mock_reply

    mocker.patch("securedrop_client.logic.storage", mock_storage)
    co.on_reply_success(reply.uuid)

    assert info_logger.call_args_list[0][0][0] == "{} sent successfully".format(reply.uuid)
    assert len(reply_succeeded_emissions) == 1
    assert reply_succeeded_emissions[0] == ["source_uuid", reply.uuid, "reply_message_mock"]
    assert len(reply_failed_emissions) == 0


def test_Controller_on_reply_failure(homedir, mocker, session_maker):
    """
    Check that when the method is called, the client emits the correct signal.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    reply_succeeded_emissions = QSignalSpy(co.reply_succeeded)
    reply_failed_emissions = QSignalSpy(co.reply_failed)
    debug_logger = mocker.patch("securedrop_client.logic.logger.debug")

    exception = SendReplyJobError("mock_error_message", "mock_reply_uuid")
    co.on_reply_failure(exception)

    debug_logger.assert_called_once_with("{} failed to send".format("mock_reply_uuid"))
    assert len(reply_failed_emissions) == 1
    assert reply_failed_emissions[0] == ["mock_reply_uuid"]
    assert len(reply_succeeded_emissions) == 0


def test_Controller_on_reply_failure_for_timeout(homedir, mocker, session_maker):
    """
    Check that when the method is called, the client emits the correct signal.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    reply_succeeded_emissions = QSignalSpy(co.reply_succeeded)
    reply_failed_emissions = QSignalSpy(co.reply_failed)
    debug_logger = mocker.patch("securedrop_client.logic.logger.debug")

    exception = SendReplyJobTimeoutError("mock_error_message", "mock_reply_uuid")
    co.on_reply_failure(exception)

    debug_logger.assert_called_once_with("{} failed to send".format("mock_reply_uuid"))
    assert len(reply_failed_emissions) == 0
    assert len(reply_succeeded_emissions) == 0


def test_Controller_is_authenticated_property(homedir, mocker, session_maker):
    """
    Check that the @property `is_authenticated`:
      - Cannot be deleted
      - Emits the correct signals when updated
      - Sets internal state to ensure signals are only set when the state changes
    """
    mock_gui = mocker.MagicMock()

    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    authentication_state_emissions = QSignalSpy(co.authentication_state)

    # default state is unauthenticated
    assert co.is_authenticated is False

    # the property cannot be deleted
    with pytest.raises(AttributeError):
        del co.is_authenticated

    # setting the signal to its current value does not fire the signal
    co.is_authenticated = False
    assert len(authentication_state_emissions) == 0
    assert co.is_authenticated is False

    # setting the property to True sends a signal
    co.is_authenticated = True
    assert len(authentication_state_emissions) == 1
    assert authentication_state_emissions[0] == [True]
    assert co.is_authenticated is True

    co.is_authenticated = False
    assert len(authentication_state_emissions) == 2
    assert authentication_state_emissions[1] == [False]
    assert co.is_authenticated is False


def test_Controller_resume_queues(homedir, mocker, session_maker):
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.api_job_queue = mocker.MagicMock()
    co.show_last_sync_timer = mocker.MagicMock()
    co.resume_queues()
    co.api_job_queue.resume_queues.assert_called_once_with()
    co.show_last_sync_timer.stop.assert_called_once_with()


@pytest.mark.parametrize("exception", [RequestTimeoutError, ServerConnectionError])
def test_APICallRunner_api_call_timeout(mocker, exception):
    """
    Ensure that if a RequestTimeoutError or ServerConnectionError is raised, both
    the failure and timeout signals are emitted.
    """
    mock_api = mocker.MagicMock()
    mock_api.fake_request = mocker.MagicMock(side_effect=exception())

    runner = APICallRunner(mock_api.fake_request)

    call_failed_emissions = QSignalSpy(runner.call_failed)
    call_timed_out_emissions = QSignalSpy(runner.call_timed_out)

    runner.call_api()

    mock_api.fake_request.assert_called_once_with()
    assert len(call_failed_emissions) == 1
    assert len(call_timed_out_emissions) == 1


def test_Controller_on_queue_paused(homedir, config, mocker, session_maker):
    """
    Check that a paused queue is communicated to the user via the error status bar
    """
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    mocker.patch.object(co, "api_job_queue")
    co.api = "not none"
    co.show_last_sync_timer = mocker.MagicMock()
    co.on_queue_paused()
    mock_gui.update_error_status.assert_called_once_with(
        "The SecureDrop server cannot be reached. Trying to reconnect...", duration=0
    )
    co.show_last_sync_timer.start.assert_called_once_with(TIME_BETWEEN_SHOWING_LAST_SYNC_MS)


def test_Controller_call_update_star_success(homedir, config, mocker, session_maker, session):
    """
    Check that a UpdateStar is submitted to the queue when update_star is called.
    """
    mock_gui = mocker.MagicMock()
    co = Controller("http://localhost", mock_gui, session_maker, homedir, None)
    co.call_api = mocker.MagicMock()
    co.api = mocker.MagicMock()

    star_update_successful = mocker.MagicMock()
    star_update_failed = mocker.MagicMock()
    mock_job = mocker.MagicMock(
        success_signal=star_update_successful, failure_signal=star_update_failed
    )
    mock_job_cls = mocker.patch("securedrop_client.logic.UpdateStarJob", return_value=mock_job)
    add_job_emissions = QSignalSpy(co.add_job)

    source = factory.Source()
    session.add(source)
    session.commit()

    co.update_star(source.uuid, source.is_starred)

    mock_job_cls.assert_called_once_with(source.uuid, source.is_starred)
    assert len(add_job_emissions) == 1
    assert add_job_emissions[0] == [mock_job]
    assert star_update_successful.connect.call_count == 1
    star_update_failed.connect.assert_called_once_with(
        co.on_update_star_failure, type=Qt.QueuedConnection
    )
    star_update_successful.connect.assert_called_once_with(
        co.on_update_star_success, type=Qt.QueuedConnection
    )


def test_Controller_run_printer_preflight_checks(homedir, mocker, session, source):
    co = Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)
    begin_printer_preflight_emissions = QSignalSpy(co.export.begin_printer_preflight)

    co.run_printer_preflight_checks()

    assert len(begin_printer_preflight_emissions) == 1


def test_Controller_run_printer_preflight_checks_not_qubes(homedir, mocker, session, source):
    co = Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)
    co.qubes = False
    begin_printer_preflight_emissions = QSignalSpy(co.export.begin_printer_preflight)
    printer_preflight_success_emissions = QSignalSpy(co.export.printer_preflight_success)

    co.run_printer_preflight_checks()

    assert len(begin_printer_preflight_emissions) == 0
    assert len(printer_preflight_success_emissions) == 1


def test_Controller_run_print_file(mocker, session, homedir):
    co = Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)
    begin_print_emissions = QSignalSpy(co.export.begin_print)
    file = factory.File(source=factory.Source())
    session.add(file)
    session.commit()
    mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)

    filepath = file.location(co.data_dir)
    os.makedirs(os.path.dirname(filepath), mode=0o700, exist_ok=True)
    with open(filepath, "w"):
        pass

    co.print_file(file.uuid)

    assert len(begin_print_emissions) == 1


def test_Controller_run_print_file_not_qubes(mocker, session, homedir):
    co = Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)
    co.qubes = False
    begin_print_emissions = QSignalSpy(co.export.begin_print)
    file = factory.File(source=factory.Source())
    session.add(file)
    session.commit()
    mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)

    filepath = file.location(co.data_dir)
    os.makedirs(os.path.dirname(filepath), mode=0o700, exist_ok=True)
    with open(filepath, "w"):
        pass

    co.print_file(file.uuid)

    assert len(begin_print_emissions) == 0


def test_Controller_print_file_file_missing(homedir, mocker, session, session_maker):
    """
    If the file is missing from the data dir, is_downloaded should be set to False and the failure
    should be communicated to the user.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    file = factory.File(source=factory.Source())
    session.add(file)
    session.commit()
    mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)
    warning_logger = mocker.patch("securedrop_client.logic.logger.warning")

    co.print_file(file.uuid)

    log_msg = "Cannot find file in {}. File does not exist.".format(os.path.dirname(file.filename))
    warning_logger.assert_called_once_with(log_msg)


def test_Controller_print_file_file_missing_not_qubes(homedir, mocker, session, session_maker):
    """
    If the file is missing from the data dir, is_downloaded should be set to False and the failure
    should be communicated to the user.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.qubes = False
    file = factory.File(source=factory.Source())
    session.add(file)
    session.commit()
    mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)
    warning_logger = mocker.patch("securedrop_client.logic.logger.warning")

    co.print_file(file.uuid)

    log_msg = "Cannot find file in {}. File does not exist.".format(os.path.dirname(file.filename))
    warning_logger.assert_called_once_with(log_msg)


def test_Controller_print_file_when_orig_file_already_exists(
    homedir, config, mocker, session, session_maker, source
):
    """
    The signal `begin_print` should still be emmited if the original file already exists.
    """
    co = Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)
    file = factory.File(source=factory.Source())
    begin_print_emissions = QSignalSpy(co.export.begin_print)
    session.add(file)
    session.commit()
    mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)
    mocker.patch("os.path.exists", return_value=True)

    co.print_file(file.uuid)

    assert len(begin_print_emissions) == 1
    co.get_file.assert_called_with(file.uuid)


def test_Controller_print_file_when_orig_file_already_exists_not_qubes(
    homedir, config, mocker, session, session_maker, source
):
    """
    The signal `begin_print` should still be emmited if the original file already exists.
    """
    co = Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)
    co.qubes = False
    begin_print_emissions = QSignalSpy(co.export.begin_print)
    file = factory.File(source=factory.Source())
    session.add(file)
    session.commit()
    mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)

    filepath = file.location(co.data_dir)
    os.makedirs(os.path.dirname(filepath), mode=0o700, exist_ok=True)
    with open(filepath, "w"):
        pass

    co.export_file_to_usb_drive(file.uuid, "mock passphrase")

    assert len(begin_print_emissions) == 0
    co.get_file.assert_called_with(file.uuid)
    co.get_file.assert_called_with(file.uuid)


def test_Controller_run_export_preflight_checks(homedir, mocker, session, source):
    co = Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)
    begin_preflight_check_emissions = QSignalSpy(co.export.begin_preflight_check)
    file = factory.File(source=source["source"])
    session.add(file)
    session.commit()
    mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)

    co.run_export_preflight_checks()

    assert len(begin_preflight_check_emissions) == 1


def test_Controller_run_export_preflight_checks_not_qubes(homedir, mocker, session, source):
    co = Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)
    co.qubes = False
    begin_preflight_check_emissions = QSignalSpy(co.export.begin_preflight_check)
    file = factory.File(source=source["source"])
    session.add(file)
    session.commit()
    mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)

    co.run_export_preflight_checks()

    assert len(begin_preflight_check_emissions) == 0


def test_Controller_export_file_to_usb_drive(homedir, mocker, session):
    """
    The signal `begin_usb_export` should be emmited during export_file_to_usb_drive.
    """
    co = Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)
    begin_usb_export_emissions = QSignalSpy(co.export.begin_usb_export)
    file = factory.File(source=factory.Source())
    session.add(file)
    session.commit()
    mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)

    filepath = file.location(co.data_dir)
    os.makedirs(os.path.dirname(filepath), mode=0o700, exist_ok=True)
    with open(filepath, "w"):
        pass

    co.export_file_to_usb_drive(file.uuid, "mock passphrase")

    assert len(begin_usb_export_emissions) == 1


def test_Controller_export_file_to_usb_drive_not_qubes(homedir, mocker, session):
    """
    The signal `begin_usb_export` should be emmited during export_file_to_usb_drive.
    """
    co = Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)
    co.qubes = False
    begin_usb_export_emissions = QSignalSpy(co.export.begin_usb_export)
    co.export.send_file_to_usb_device = mocker.MagicMock()
    file = factory.File(source=factory.Source())
    session.add(file)
    session.commit()
    mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)

    filepath = file.location(co.data_dir)
    os.makedirs(os.path.dirname(filepath), mode=0o700, exist_ok=True)
    with open(filepath, "w"):
        pass

    co.export_file_to_usb_drive(file.uuid, "mock passphrase")

    co.export.send_file_to_usb_device.assert_not_called()
    assert len(begin_usb_export_emissions) == 0


def test_Controller_export_file_to_usb_drive_file_missing(homedir, mocker, session, session_maker):
    """
    If the file is missing from the data dir, is_downloaded should be set to False and the failure
    should be communicated to the user.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    file = factory.File(source=factory.Source())
    session.add(file)
    session.commit()
    mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)
    warning_logger = mocker.patch("securedrop_client.logic.logger.warning")

    co.export_file_to_usb_drive(file.uuid, "mock passphrase")

    log_msg = "Cannot find file in {}. File does not exist.".format(os.path.dirname(file.filename))
    warning_logger.assert_called_once_with(log_msg)


def test_Controller_export_file_to_usb_drive_file_missing_not_qubes(
    homedir, mocker, session, session_maker
):
    """
    If the file is missing from the data dir, is_downloaded should be set to False and the failure
    should be communicated to the user.
    """
    co = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir, None)
    co.qubes = False
    file = factory.File(source=factory.Source())
    session.add(file)
    session.commit()
    mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)
    warning_logger = mocker.patch("securedrop_client.logic.logger.warning")

    co.export_file_to_usb_drive(file.uuid, "mock passphrase")

    log_msg = "Cannot find file in {}. File does not exist.".format(os.path.dirname(file.filename))
    warning_logger.assert_called_once_with(log_msg)


def test_Controller_export_file_to_usb_drive_when_orig_file_already_exists(
    homedir, config, mocker, session, session_maker, source
):
    """
    The signal `begin_usb_export` should still be emmited if the original file already exists.
    """
    co = Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)
    begin_usb_export_emissions = QSignalSpy(co.export.begin_usb_export)
    file = factory.File(source=factory.Source())
    session.add(file)
    session.commit()
    mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)
    mocker.patch("os.path.exists", return_value=True)

    co.export_file_to_usb_drive(file.uuid, "mock passphrase")

    assert len(begin_usb_export_emissions) == 1
    co.get_file.assert_called_with(file.uuid)


def test_Controller_export_file_to_usb_drive_when_orig_file_already_exists_not_qubes(
    homedir, config, mocker, session, session_maker, source
):
    """
    The signal `begin_usb_export` should still be emmited if the original file already exists.
    """
    co = Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)
    co.qubes = False
    begin_usb_export_emissions = QSignalSpy(co.export.begin_usb_export)
    file = factory.File(source=factory.Source())
    session.add(file)
    session.commit()
    mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)

    filepath = file.location(co.data_dir)
    os.makedirs(os.path.dirname(filepath), mode=0o700, exist_ok=True)
    with open(filepath, "w"):
        pass

    co.export_file_to_usb_drive(file.uuid, "mock passphrase")

    assert len(begin_usb_export_emissions) == 0
    co.get_file.assert_called_with(file.uuid)


def test_get_file(mocker, session, homedir):
    co = Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)
    storage = mocker.patch("securedrop_client.logic.storage")
    file = factory.File(source=factory.Source())
    session.add(file)
    session.commit()
    storage.get_file = mocker.MagicMock(return_value=file)

    obj = co.get_file(file.uuid)

    storage.get_file.assert_called_once_with(co.session, file.uuid)
    assert obj == file
