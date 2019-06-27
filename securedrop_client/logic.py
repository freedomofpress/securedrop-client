"""
Contains the core logic for the application in the Controller class.

Copyright (C) 2018  The Freedom of the Press Foundation.

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published
by the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <fhttp://www.gnu.org/licenses/>.
"""
import arrow
import inspect
import logging
import os
import sdclientapi
import uuid
from typing import Dict, Tuple, Union, Any, Type  # noqa: F401

from gettext import gettext as _
from PyQt5.QtCore import QObject, QThread, pyqtSignal, QTimer, QProcess, Qt
from sdclientapi import RequestTimeoutError
from sqlalchemy.orm.session import sessionmaker

from securedrop_client import storage
from securedrop_client import db
from securedrop_client.api_jobs.downloads import FileDownloadJob, MessageDownloadJob, \
    ReplyDownloadJob
from securedrop_client.api_jobs.uploads import SendReplyJob, SendReplyJobException
from securedrop_client.api_jobs.updatestar import UpdateStarJob, UpdateStarJobException
from securedrop_client.crypto import GpgHelper, CryptoError
from securedrop_client.queue import ApiJobQueue
from securedrop_client.utils import check_dir_permissions

logger = logging.getLogger(__name__)


class APICallRunner(QObject):
    """
    Used to call the SecureDrop API in a non-blocking manner.

    See the call_api method of the Controller class for how this is
    done (hint: you should be using the call_api method and not directly
    using this class).
    """

    call_succeeded = pyqtSignal()
    call_failed = pyqtSignal()
    call_timed_out = pyqtSignal()

    def __init__(self, api_call, current_object=None, *args, **kwargs):
        """
        Initialise with the function to call the API and any associated
        args and kwargs. If current object is passed in, this represents some
        state which the event handlers may need when they're eventually fired.
        """
        super().__init__()
        self.api_call = api_call
        self.current_object = current_object
        self.args = args
        self.kwargs = kwargs
        self.result = None

    def call_api(self):
        """
        Call the API. Emit a boolean signal to indicate the outcome of the
        call. Any return value or exception raised is stored in self.result.
        """
        # this blocks
        try:
            self.result = self.api_call(*self.args, **self.kwargs)
        except Exception as ex:
            if isinstance(ex, RequestTimeoutError):
                self.call_timed_out.emit()

            logger.error(ex)
            self.result = ex
            self.call_failed.emit()
        else:
            self.call_succeeded.emit()


class Controller(QObject):
    """
    Represents the logic for the secure drop client application. In an MVC
    application, this is the controller.
    """

    sync_events = pyqtSignal(str)

    """
    Signal that notifies that a reply was accepted by the server. Emits the reply's UUID as a
    string.
    """
    reply_succeeded = pyqtSignal(str)

    """
    Signal that notifies that a reply failed to be accepted by the server. Emits the reply's UUID
    as a string.
    """
    reply_failed = pyqtSignal(str)

    """
    A signal that emits a signal when the authentication state changes.
    - `True` when the client becomes authenticated
    - `False` when the client becomes unauthenticated
    """
    authentication_state = pyqtSignal(bool)

    """
    This signal indicates that a file has been successfully downloaded by emitting the file's
    UUID as a string.
    """
    file_ready = pyqtSignal(str)

    """
    This signal indicates that a message has been successfully downloaded by emitting the message's
    UUID as a string.
    """
    message_ready = pyqtSignal([str, str])

    """
    This signal indicates that a reply has been successfully downloaded by emitting the reply's
    UUID as a string.
    """
    reply_ready = pyqtSignal([str, str])

    def __init__(self, hostname: str, gui, session_maker: sessionmaker,
                 home: str, proxy: bool = True) -> None:
        """
        The hostname, gui and session objects are used to coordinate with the
        various other layers of the application: the location of the SecureDrop
        proxy, the user interface and SqlAlchemy local storage respectively.
        """
        check_dir_permissions(home)
        super().__init__()

        # Controller is unauthenticated by default
        self.__is_authenticated = False

        # used for finding DB in sync thread
        self.home = home

        # boolean flag for whether or not the client is operating behind a proxy
        self.proxy = proxy

        # Location of the SecureDrop server.
        self.hostname = hostname

        # Reference to the UI window.
        self.gui = gui

        # Reference to the API for secure drop proxy.
        self.api = None  # type: sdclientapi.API

        # Reference to the SqlAlchemy `sessionmaker` and `session`
        self.session_maker = session_maker
        self.session = session_maker()

        # Queue that handles running API job
        self.api_job_queue = ApiJobQueue(self.api, self.session_maker)

        # Contains active threads calling the API.
        self.api_threads = {}  # type: Dict[str, Dict]

        self.gpg = GpgHelper(home, self.session_maker, proxy)

        self.sync_flag = os.path.join(home, 'sync_flag')

        # File data.
        self.data_dir = os.path.join(self.home, 'data')

    @property
    def is_authenticated(self) -> bool:
        return self.__is_authenticated

    @is_authenticated.setter
    def is_authenticated(self, is_authenticated: bool) -> None:
        if self.__is_authenticated != is_authenticated:
            self.authentication_state.emit(is_authenticated)
            self.__is_authenticated = is_authenticated

    @is_authenticated.deleter
    def is_authenticated(self) -> None:
        raise AttributeError('Cannot delete is_authenticated')

    def setup(self):
        """
        Setup the application with the default state of:

        * Not logged in.
        * Show most recent state of syncronised sources.
        * Show the login screen.
        * Check the sync status every 30 seconds.
        """
        # The gui needs to reference this "controller" layer to call methods
        # triggered by UI events.
        self.gui.setup(self)

        # Create a timer to check for sync status every 30 seconds.
        self.sync_timer = QTimer()
        self.sync_timer.timeout.connect(self.update_sync)
        self.sync_timer.start(30000)

        # Automagically sync with the API every 5 minutes.
        self.sync_update = QTimer()
        self.sync_update.timeout.connect(self.sync_api)
        self.sync_update.start(1000 * 60 * 5)  # every 5 minutes.

    def call_api(self,
                 api_call_func,
                 success_callback,
                 failure_callback,
                 *args,
                 current_object=None,
                 **kwargs):
        """
        Calls the function in a non-blocking manner. Upon completion calls the
        callback with the result. Calls timeout if the timer associated with
        the call emits a timeout signal. Any further arguments are passed to
        the function to be called.
        """
        new_thread_id = str(uuid.uuid4())  # Uniquely id the new thread.

        new_api_thread = QThread(self.gui)
        new_api_runner = APICallRunner(api_call_func, current_object, *args,
                                       **kwargs)
        new_api_runner.moveToThread(new_api_thread)

        # handle completed call: copy response data, reset the
        # client, give the user-provided callback the response
        # data
        new_api_runner.call_succeeded.connect(
            lambda: self.completed_api_call(new_thread_id, success_callback))
        new_api_runner.call_failed.connect(
            lambda: self.completed_api_call(new_thread_id, failure_callback))
        new_api_runner.call_timed_out.connect(self.on_api_timeout)

        # when the thread starts, we want to run `call_api` on `api_runner`
        new_api_thread.started.connect(new_api_runner.call_api)

        # Add the thread related objects to the api_threads dictionary.
        self.api_threads[new_thread_id] = {
            'thread': new_api_thread,
            'runner': new_api_runner,
        }

        # Start the thread and related activity.
        new_api_thread.start()

    def on_api_timeout(self) -> None:
        self.gui.update_error_status(_('The connection to the SecureDrop server timed out. '
                                       'Please try again.'))

    def completed_api_call(self, thread_id, user_callback):
        """
        Manage a completed API call. The actual result *may* be an exception or
        error result from the API. It's up to the handler (user_callback) to
        handle these potential states.
        """
        logger.info("Completed API call. Cleaning up and running callback.")
        thread_info = self.api_threads.pop(thread_id)
        runner = thread_info['runner']
        result_data = runner.result

        arg_spec = inspect.getfullargspec(user_callback)
        if 'current_object' in arg_spec.args:
            user_callback(result_data, current_object=runner.current_object)
        else:
            user_callback(result_data)

    def login(self, username, password, totp):
        """
        Given a username, password and time based one-time-passcode (TOTP),
        create a new instance representing the SecureDrop api and authenticate.
        """
        self.api = sdclientapi.API(self.hostname, username,
                                   password, totp, self.proxy)
        self.call_api(self.api.authenticate,
                      self.on_authenticate_success,
                      self.on_authenticate_failure)

    def on_authenticate_success(self, result):
        """
        Handles a successful authentication call against the API.
        """
        logger.info('{} successfully logged in'.format(self.api.username))
        self.gui.hide_login()
        self.sync_api()
        self.gui.show_main_window(self.api.username)
        self.api_job_queue.login(self.api)

        # Clear the sidebar error status bar if a message was shown
        # to the user indicating they should log in.
        self.gui.clear_error_status()

        self.is_authenticated = True

    def on_authenticate_failure(self, result: Exception) -> None:
        # Failed to authenticate. Reset state with failure message.
        self.api = None
        error = _('There was a problem signing in. '
                  'Please verify your credentials and try again.')
        self.gui.show_login_error(error=error)

    def login_offline_mode(self):
        """
        Allow user to view in offline mode without authentication.
        """
        self.gui.hide_login()
        self.gui.show_main_window()
        self.is_authenticated = False
        self.update_sources()

    def on_action_requiring_login(self):
        """
        Indicate that a user needs to login to perform the specified action.
        """
        error = _('You must sign in to perform this action.')
        self.gui.update_error_status(error)

    def authenticated(self):
        """
        Return a boolean indication that the connection to the API is
        authenticated.
        """
        return bool(self.api and self.api.token is not None)

    def sync_api(self):
        """
        Grab data from the remote SecureDrop API in a non-blocking manner.
        """
        logger.debug("In sync_api on thread {}".format(self.thread().currentThreadId()))
        self.sync_events.emit('syncing')

        if self.authenticated():
            logger.debug("You are authenticated, going to make your call")
            self.call_api(storage.get_remote_data,
                          self.on_sync_success,
                          self.on_sync_failure,
                          self.api)
            logger.debug("In sync_api, after call to call_api, on "
                         "thread {}".format(self.thread().currentThreadId()))

    def last_sync(self):
        """
        Returns the time of last synchronisation with the remote SD server.
        """
        try:
            with open(self.sync_flag) as f:
                return arrow.get(f.read())
        except Exception:
            return None

    def on_sync_success(self, result) -> None:
        """
        Called when syncronisation of data via the API succeeds
        """
        # Update db with new metadata
        remote_sources, remote_submissions, remote_replies = result
        storage.update_local_storage(self.session,
                                     remote_sources,
                                     remote_submissions,
                                     remote_replies,
                                     self.data_dir)

        # Set last sync flag
        with open(self.sync_flag, 'w') as f:
            f.write(arrow.now().format())

        # Import keys into keyring
        for source in remote_sources:
            if source.key and source.key.get('type', None) == 'PGP':
                pub_key = source.key.get('public', None)
                fingerprint = source.key.get('fingerprint', None)
                if not pub_key or not fingerprint:
                    continue
                try:
                    self.gpg.import_key(source.uuid, pub_key, fingerprint)
                except CryptoError:
                    logger.warning('Failed to import key for source {}'.format(source.uuid))

        self.update_sources()
        self.download_new_messages()
        self.download_new_replies()
        self.sync_events.emit('synced')

    def on_sync_failure(self, result: Exception) -> None:
        """
        Called when syncronisation of data via the API fails.
        """
        logger.debug('Sync failed: "{}".'.format(result))

    def update_sync(self):
        """
        Updates the UI to show human time of last sync.
        """
        self.gui.show_sync(self.last_sync())

    def update_sources(self):
        """
        Display the updated list of sources with those found in local storage.
        """
        sources = list(storage.get_local_sources(self.session))
        if sources:
            sources.sort(key=lambda x: x.last_updated, reverse=True)
        self.gui.show_sources(sources)
        self.update_sync()

    def on_update_star_success(self, result) -> None:
        """
        After we star a source, we should sync the API such that the local database is updated.
        """
        self.sync_api()  # Syncing the API also updates the source list UI
        self.gui.clear_error_status()

    def on_update_star_failure(self, result: UpdateStarJobException) -> None:
        """
        After we unstar a source, we should sync the API such that the local database is updated.
        """
        logging.info("failed to push change to server")
        error = _('Failed to update star.')
        self.gui.update_error_status(error)

    def update_star(self, source_db_object):
        """
        Star or unstar. The callback here is the API sync as we first make sure
        that we apply the change to the server, and then update locally.
        """
        if not self.api:  # Then we should tell the user they need to login.
            self.on_action_requiring_login()
            return
        else:  # Clear the error status bar
            self.gui.clear_error_status()

        job = UpdateStarJob(
                source_db_object.uuid,
                source_db_object.is_starred
        )
        job.success_signal.connect(self.on_update_star_success, type=Qt.QueuedConnection)
        job.failure_signal.connect(self.on_update_star_failure, type=Qt.QueuedConnection)

        self.api_job_queue.enqueue(job)

    def logout(self):
        """
        Call logout function in the API, reset the API object, and force the UI
        to update into a logged out state.
        """
        self.call_api(self.api.logout,
                      self.on_logout_success,
                      self.on_logout_failure)
        self.api = None
        self.api_job_queue.logout()
        self.gui.logout()
        self.is_authenticated = False

    def set_status(self, message, duration=5000):
        """
        Set a textual status message to be displayed to the user for a certain
        duration.
        """
        self.gui.update_activity_status(message, duration)

    def download_new_messages(self) -> None:
        messages = storage.find_new_messages(self.session)

        if len(messages) > 0:
            self.set_status(_('Downloading new messages'))

        for message in messages:
            job = MessageDownloadJob(message.uuid, self.data_dir, self.gpg)
            job.success_signal.connect(self.on_message_download_success, type=Qt.QueuedConnection)
            job.failure_signal.connect(self.on_message_download_failure, type=Qt.QueuedConnection)
            self.api_job_queue.enqueue(job)

    def on_message_download_success(self, uuid: str) -> None:
        """
        Called when a message has downloaded.
        """
        message = storage.get_message(self.session, uuid)
        self.message_ready.emit(message.uuid, message.content)

    def on_message_download_failure(self, exception: Exception) -> None:
        """
        Called when a message fails to download.
        """
        logger.debug('Failed to download message: {}'.format(exception))

    def download_new_replies(self) -> None:
        replies = storage.find_new_replies(self.session)
        for reply in replies:
            job = ReplyDownloadJob(reply.uuid, self.data_dir, self.gpg)
            job.success_signal.connect(self.on_reply_download_success, type=Qt.QueuedConnection)
            job.failure_signal.connect(self.on_reply_download_failure, type=Qt.QueuedConnection)
            self.api_job_queue.enqueue(job)

    def on_reply_download_success(self, uuid: str) -> None:
        """
        Called when a reply has downloaded.
        """
        reply = storage.get_reply(self.session, uuid)
        self.reply_ready.emit(reply.uuid, reply.content)

    def on_reply_download_failure(self, exception: Exception) -> None:
        """
        Called when a reply fails to download.
        """
        logger.debug('Failed to download reply: {}'.format(exception))

    def on_file_open(self, file_uuid: str) -> None:
        """
        Open the already downloaded file associated with the message (which is a `File`).
        """
        # Once downloaded, submissions are stored in the data directory
        # with the same filename as the server, except with the .gz.gpg
        # stripped off.
        file = self.get_file(file_uuid)
        fn_no_ext, _ = os.path.splitext(os.path.splitext(file.filename)[0])
        submission_filepath = os.path.join(self.data_dir, fn_no_ext)

        if self.proxy:
            # Running on Qubes.
            command = "qvm-open-in-vm"
            args = ['$dispvm:sd-svs-disp', submission_filepath]

            # QProcess (Qt) or Python's subprocess? Who cares? They do the
            # same thing. :-)
            process = QProcess(self)
            process.start(command, args)
        else:  # pragma: no cover
            # Non Qubes OS. Just log the event for now.
            logger.info('Opening file "{}".'.format(submission_filepath))

    def on_submission_download(
        self,
        submission_type: Union[Type[db.File], Type[db.Message]],
        submission_uuid: str,
    ) -> None:
        """
        Download the file associated with the Submission (which may be a File or Message).
        """
        if self.api:
            job = FileDownloadJob(
                submission_uuid,
                self.data_dir,
                self.gpg,
            )
            job.success_signal.connect(self.on_file_download_success, type=Qt.QueuedConnection)
            job.failure_signal.connect(self.on_file_download_failure, type=Qt.QueuedConnection)

            self.api_job_queue.enqueue(job)
            self.set_status(_('Downloading file'))
        else:
            self.on_action_requiring_login()

    def on_file_download_success(self, result: Any) -> None:
        """
        Called when a file has downloaded.
        """
        self.file_ready.emit(result)

    def on_file_download_failure(self, exception: Exception) -> None:
        """
        Called when a file fails to download.
        """
        self.set_status(_('The file download failed. Please try again.'))

    def on_delete_source_success(self, result) -> None:
        """
        Handler for when a source deletion succeeds.
        """
        self.sync_api()
        self.gui.clear_error_status()

    def on_delete_source_failure(self, result: Exception) -> None:
        logging.info("failed to delete source at server")
        error = _('Failed to delete source at server')
        self.gui.update_error_status(error)

    def delete_source(self, source):
        """Performs a delete operation on source record.

        This method will first request server to delete the source record. If
        the process of deleting record at server is successful, it will sync
        the server records with the local state. On failure, it will display an
        error.
        """
        self.call_api(
            self.api.delete_source,
            self.on_delete_source_success,
            self.on_delete_source_failure,
            source
        )

    def send_reply(self, source_uuid: str, reply_uuid: str, message: str) -> None:
        """
        Send a reply to a source.
        """
        job = SendReplyJob(
            source_uuid,
            reply_uuid,
            message,
            self.gpg,
        )
        job.success_signal.connect(self.on_reply_success, type=Qt.QueuedConnection)
        job.failure_signal.connect(self.on_reply_failure, type=Qt.QueuedConnection)

        self.api_job_queue.enqueue(job)

    def on_reply_success(self, reply_uuid: str) -> None:
        logger.debug('{} sent successfully'.format(reply_uuid))
        self.reply_succeeded.emit(reply_uuid)

    def on_reply_failure(self, exception: SendReplyJobException) -> None:
        logger.debug('{} failed to send'.format(exception.reply_uuid))
        self.reply_failed.emit(exception.reply_uuid)

    def get_file(self, file_uuid: str) -> db.File:
        file = storage.get_file(self.session, file_uuid)
        self.session.refresh(file)
        return file

    def on_logout_success(self, result) -> None:
        logging.info('Client logout successful')

    def on_logout_failure(self, result: Exception) -> None:
        logging.info('Client logout failure')
