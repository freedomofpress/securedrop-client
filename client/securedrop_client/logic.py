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
along with this program.  If not, see <http://www.gnu.org/licenses/>.
"""

import functools
import inspect
import logging
import os
import uuid
from datetime import datetime
from gettext import gettext as _
from gettext import ngettext

import arrow
import sqlalchemy.orm.exc
from PyQt5.QtCore import QObject, QProcess, QThread, QTimer, pyqtSignal, pyqtSlot
from sqlalchemy.orm.session import sessionmaker

from securedrop_client import db, sdk, state, storage
from securedrop_client.api_jobs.base import ApiInaccessibleError
from securedrop_client.api_jobs.downloads import (
    DownloadChecksumMismatchException,
    DownloadDecryptionException,
    DownloadException,
    FileDownloadJob,
    MessageDownloadJob,
    ReplyDownloadJob,
)
from securedrop_client.api_jobs.seen import SeenJob
from securedrop_client.api_jobs.sources import (
    DeleteConversationJob,
    DeleteConversationJobException,
    DeleteSourceJob,
    DeleteSourceJobException,
)
from securedrop_client.api_jobs.updatestar import (
    UpdateStarJob,
    UpdateStarJobError,
    UpdateStarJobTimeoutError,
)
from securedrop_client.api_jobs.uploads import (
    SendReplyJob,
    SendReplyJobError,
    SendReplyJobTimeoutError,
)
from securedrop_client.crypto import GpgHelper
from securedrop_client.queue import ApiJobQueue
from securedrop_client.sdk import AuthError, RequestTimeoutError, ServerConnectionError
from securedrop_client.sync import ApiSync
from securedrop_client.utils import check_dir_permissions

logger = logging.getLogger(__name__)

# 30 seconds between showing the time since the last sync
LAST_SYNC_REFRESH_INTERVAL_MS = 1000 * 30


def login_required(f):  # type: ignore[no-untyped-def]
    @functools.wraps(f)
    def decorated_function(self, *args, **kwargs):  # type: ignore[no-untyped-def]
        if not self.api:
            self.on_action_requiring_login()
            return None
        else:
            return f(self, *args, **kwargs)

    return decorated_function


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

    def __init__(  # type: ignore[no-untyped-def]
        self, api_call, current_object=None, *args, **kwargs
    ):
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

    def call_api(self) -> None:
        """
        Call the API. Emit a boolean signal to indicate the outcome of the
        call. Any return value or exception raised is stored in self.result.
        """
        # this blocks
        try:
            self.result = self.api_call(*self.args, **self.kwargs)
        except Exception as ex:
            if isinstance(ex, RequestTimeoutError | ServerConnectionError):
                self.call_timed_out.emit()

            logger.error("Call failed")
            logger.debug(f"Call failed: {ex}")
            self.result = ex
            self.call_failed.emit()
        else:
            self.call_succeeded.emit()


class Controller(QObject):
    """
    Represents the logic for the secure drop client application. In an MVC
    application, this is the controller.
    """

    """
    This signal indicates when a sync has started.

    Emits:
        datetime: the time that the sync started
    """
    sync_started = pyqtSignal(datetime)

    """
    This signal indicates when a sync has successfully completed.
    """
    sync_succeeded = pyqtSignal()

    """
    This signal indicates when the authentication state changes.

    Emits:
        bool: is_authenticated
    """
    authentication_state = pyqtSignal(bool)

    """
    This signal indicates that the authenticated user info has changed.

    Emits:
       db.User: the authenticated user
    """
    update_authenticated_user = pyqtSignal(db.User)

    """
    This signal indicates that a reply was successfully sent and received by the server.

    Emits:
        str: the reply's source UUID
        str: the reply UUID
        str: the content of the reply
    """
    reply_succeeded = pyqtSignal(str, str, str)

    """
    This signal indicates that a reply was not successfully sent or received by the server.

    Emits:
        str: the reply UUID
    """
    reply_failed = pyqtSignal(str)

    """
    This signal indicates that a reply has been successfully downloaded.

    Emits:
        str: the reply's source UUID
        str: the reply UUID
        str: the content of the reply
    """
    reply_ready = pyqtSignal(str, str, str)

    """
    This signal indicates an error while downloading a reply.

    Emits:
        str: the reply's source UUID
        str: the reply UUID
        str: the content of the reply
    """
    reply_download_failed = pyqtSignal(str, str, str)

    """
    This signal indicates that a message has been successfully downloaded.

    Emits:
        str: the message's source UUID
        str: the message UUID
        str: the content of the message
    """
    message_ready = pyqtSignal(str, str, str)

    """
    This signal indicates an error while downloading a message.

    Emits:
        str: the message's source UUID
        str: the message UUID
        str: the content of the message
    """
    message_download_failed = pyqtSignal(str, str, str)

    file_download_started = pyqtSignal(state.FileId)

    """
    This signal indicates that a file has been successfully downloaded.

    Emits:
        str: the file's source UUID
        str: the file UUID
        str: the name of the file
    """
    file_ready = pyqtSignal(str, str, str)

    """
    This signal indicates that a file is missing.

    Emits:
        str: the file UUID
    """
    file_missing = pyqtSignal(str, str, str)

    """
    This signal indicates that a deletion request was accepted by the server.

    Emits:
        str: the source UUID
    """
    source_deleted = pyqtSignal(str)

    """
    Indicates that a source conversation content deletion request was sent to the server.

    Emits:
        str: the source UUID
    """
    conversation_deleted = pyqtSignal(str)

    """
    Indicates that a source conversation content deletion attempt failed at the server.

    Emits:
        str: the source UUID
    """
    conversation_deletion_failed = pyqtSignal(str)

    """
    This signal indicates that a star update request succeeded.

    Emits:
        str: the source UUID
    """
    star_update_successful = pyqtSignal(str)

    """
    This signal indicates that a star update request failed.

    Emits:
        str: the source UUID
        bool: is_starred
    """
    star_update_failed = pyqtSignal(str, bool)

    """
    This signal indicates that a deletion attempt failed at the server.

    Emits:
        str: the source UUID
    """
    source_deletion_failed = pyqtSignal(str)

    """
    This signal indicates that a deletion attempt was successful at the server.

    Emits:
        str: the source UUID
        datetime: the timestamp for when the deletion succeeded
    """
    conversation_deletion_successful = pyqtSignal(str, datetime)

    """
    This signal lets the queue manager know to add the job to the appropriate
    network queue.

    Emits:
        PyQt_PyObject: the ApiJob to be added
    """
    add_job = pyqtSignal("PyQt_PyObject")

    def __init__(  # type: ignore[no-untyped-def]
        self,
        hostname: str,
        gui,
        session_maker: sessionmaker,
        home: str,
        state: state.State,
        proxy: bool = True,
        qubes: bool = True,
        sync_thread: QThread | None = None,
        main_queue_thread: QThread | None = None,
        file_download_queue_thread: QThread | None = None,
    ) -> None:
        """
        The hostname, gui and session objects are used to coordinate with the
        various other layers of the application: the location of the SecureDrop
        proxy, the user interface and SqlAlchemy local storage respectively.
        """
        check_dir_permissions(home)
        super().__init__()

        self._state = state

        if sync_thread is not None:
            self.sync_thread = sync_thread
        else:
            self.sync_thread = QThread()

        if main_queue_thread is not None:
            self.main_queue_thread = main_queue_thread
        else:
            self.main_queue_thread = QThread()

        if file_download_queue_thread is not None:
            self.file_download_queue_thread = file_download_queue_thread
        else:
            self.file_download_queue_thread = QThread()

        # Controller is unauthenticated by default
        self.__is_authenticated = False

        # used for finding DB in sync thread
        self.home = home

        # boolean flag for whether or not the client is operating behind a proxy
        self.proxy = proxy

        # boolean flag for whether the client is running within Qubes
        # (regardless of proxy state, to support local dev in an AppVM)
        self.qubes = qubes

        # Location of the SecureDrop server.
        self.hostname = hostname

        # Reference to the UI window.
        self.gui = gui

        # Reference to the API for secure drop proxy.
        self.api: sdk.API | None = None

        # Store authenticated user
        self.authenticated_user: db.User | None = None

        # Reference to the SqlAlchemy `sessionmaker` and `session`
        self.session_maker = session_maker
        self.session = session_maker()

        # Queue that handles running API job
        self.api_job_queue = ApiJobQueue(
            self.api, self.session_maker, self.main_queue_thread, self.file_download_queue_thread
        )
        self.api_job_queue.cleared.connect(self.on_queue_cleared)
        self.api_job_queue.paused.connect(self.on_queue_paused)
        self.api_job_queue.main_queue_updated.connect(self._on_main_queue_updated)
        self.add_job.connect(self.api_job_queue.enqueue)

        # Contains active threads calling the API.
        self.api_threads = {}  # type: dict[str, dict]

        self.gpg = GpgHelper(home, self.session_maker, proxy)

        # File data.
        self.data_dir = os.path.join(self.home, "data")

        # Background sync to keep client up-to-date with server changes
        self.api_sync = ApiSync(
            self.api, self.session_maker, self.gpg, self.data_dir, self.sync_thread, state
        )
        self.api_sync.sync_started.connect(self.on_sync_started)
        self.api_sync.sync_success.connect(self.on_sync_success)
        self.api_sync.sync_failure.connect(self.on_sync_failure)

        # Create a timer to show the time since the last sync
        self.show_last_sync_timer = QTimer()
        self.show_last_sync_timer.timeout.connect(self.show_last_sync)
        self.show_last_sync_timer.start(LAST_SYNC_REFRESH_INTERVAL_MS)
        self.show_last_sync()

        # Path to the file containing the timestamp since the last sync with the server
        # TODO: Remove this code once the sync timestamp is tracked instead in svs.sqlite
        self.last_sync_filepath = os.path.join(home, "sync_flag")
        if (
            os.path.exists(self.last_sync_filepath)
            and oct(os.stat(self.last_sync_filepath).st_mode) != "0o100600"
        ):
            os.chmod(self.last_sync_filepath, 0o600)

        # Store currently-selected sources
        self._selected_sources: list[db.Source] | None = None

    @pyqtSlot(int)
    def _on_main_queue_updated(self, num_items: int) -> None:
        if num_items > 0:
            status_text = ngettext(
                "Retrieving 1 message", "Retrieving {message_count} messages", num_items
            ).format(message_count=num_items)
        else:
            status_text = ""
        self.set_status(status_text, 0)

    @property
    def is_authenticated(self) -> bool:
        return self.__is_authenticated

    @is_authenticated.setter
    def is_authenticated(self, is_authenticated: bool) -> None:
        if self.__is_authenticated != is_authenticated:
            self.__is_authenticated = is_authenticated
            self.authentication_state.emit(is_authenticated)

    @is_authenticated.deleter
    def is_authenticated(self) -> None:
        raise AttributeError("Cannot delete is_authenticated")

    def setup(self) -> None:
        """
        Setup the application with the default state of:

        * Not logged in.
        * Show most recent state of synchronized sources.
        * Show the login screen.
        """
        # The gui needs to reference this "controller" layer to call methods
        # triggered by UI events.
        self.gui.setup(self)

        storage.clear_download_errors(self.session)

    def call_api(  # type: ignore[no-untyped-def]
        self,
        api_call_func,
        success_callback,
        failure_callback,
        *args,
        current_object=None,
        **kwargs,
    ):
        """
        Calls the function in a non-blocking manner. Upon completion calls the
        callback with the result. Any further arguments are passed to
        the function to be called.
        """
        new_thread_id = str(uuid.uuid4())  # Uniquely id the new thread.

        new_api_thread = QThread(self.gui)
        new_api_runner = APICallRunner(api_call_func, current_object, *args, **kwargs)
        new_api_runner.moveToThread(new_api_thread)

        # handle completed call: copy response data, reset the
        # client, give the user-provided callback the response
        # data
        new_api_runner.call_succeeded.connect(
            lambda: self.completed_api_call(new_thread_id, success_callback)
        )
        new_api_runner.call_failed.connect(
            lambda: self.completed_api_call(new_thread_id, failure_callback)
        )

        # when the thread starts, we want to run `call_api` on `api_runner`
        new_api_thread.started.connect(new_api_runner.call_api)

        # Add the thread related objects to the api_threads dictionary.
        self.api_threads[new_thread_id] = {"thread": new_api_thread, "runner": new_api_runner}

        # Start the thread and related activity.
        new_api_thread.start()

    def on_queue_cleared(self) -> None:
        self.update_failed_replies()

    def on_queue_paused(self) -> None:
        self.gui.update_error_status(
            _("The SecureDrop server cannot be reached. Trying to reconnect..."), duration=0
        )

    def resume_queues(self) -> None:
        self.api_job_queue.resume_queues()

        # clear error status in case queue was paused resulting in a permanent error message
        self.gui.clear_error_status()

    def completed_api_call(self, thread_id, user_callback):  # type: ignore[no-untyped-def]
        """
        Manage a completed API call. The actual result *may* be an exception or
        error result from the API. It's up to the handler (user_callback) to
        handle these potential states.
        """
        logger.debug("Completed API call. Cleaning up and running callback.")
        thread_info = self.api_threads.pop(thread_id)
        runner = thread_info["runner"]
        result_data = runner.result

        arg_spec = inspect.getfullargspec(user_callback)
        if "current_object" in arg_spec.args:
            user_callback(result_data, current_object=runner.current_object)
        else:
            user_callback(result_data)

        thread = thread_info["thread"]
        thread.exit()
        # Wait until the thread has finished, or the deadline expires.
        TWO_SECONDS_IN_MILLISECONDS = 2000
        thread.wait(TWO_SECONDS_IN_MILLISECONDS)

    def login(self, username: str, password: str, totp: str) -> None:
        """
        Given a username, password and time based one-time-passcode (TOTP), create a new instance
        representing the SecureDrop api and authenticate.

        Default to 60 seconds until we implement a better request timeout strategy. We lower the
        default_request_timeout for Queue API requests in ApiJobQueue in order to display errors
        faster.
        """
        self.api = sdk.API(
            self.hostname, username, password, totp, self.proxy, default_request_timeout=60
        )
        self.call_api(
            self.api.authenticate, self.on_authenticate_success, self.on_authenticate_failure
        )

    def on_authenticate_success(self, result):  # type: ignore[no-untyped-def]
        """
        Handles a successful authentication call against the API.
        """
        # First set is_authenticated before calling GUI methods or emitting signals to the GUI
        # since the GUI has to check authentication state in several places.
        self.is_authenticated = True

        logger.info(f"{self.api.username} successfully logged in")
        self.gui.hide_login()
        user = storage.create_or_update_user(
            self.api.token_journalist_uuid,
            self.api.username,
            self.api.first_name,
            self.api.last_name,
            self.session,
        )

        self.authenticated_user = user
        self.update_authenticated_user.emit(user)

        # Clear clipboard contents in case of previously pasted creds
        self.gui.clear_clipboard()
        self.gui.show_main_window(user)
        self.update_sources()
        self.api_job_queue.start(self.api)
        self.api_sync.start(self.api)

    def on_authenticate_failure(self, result: Exception) -> None:
        # Failed to authenticate. Reset state with failure message.
        self.invalidate_token()

        if isinstance(result, RequestTimeoutError | ServerConnectionError):
            error = _(
                "Could not reach the SecureDrop server. Please check your \n"
                "Internet and Tor connection and try again."
            )
        elif isinstance(result, AuthError):
            error = _(
                "Those credentials didn't work. Please try again, and \n"
                "make sure to use a new two-factor code."
            )
        else:
            error = _("That didn't work. Please check everything and try again.")

        self.gui.show_login_error(error=error)
        self.api_sync.stop()

    def login_offline_mode(self) -> None:
        """
        Allow user to view in offline mode without authentication.
        """
        # First set is_authenticated before calling GUI methods or emitting signals to the GUI
        # since the GUI has to check authentication state in several places.
        self.is_authenticated = False
        self.gui.hide_login()
        # Clear clipboard contents in case of previously pasted creds (user
        # may have attempted online mode login, then switched to offline)
        self.gui.clear_clipboard()
        self.gui.show_main_window()

        # All child elements of main window should show logged_out state
        self.gui.logout()
        self.update_sources()

    def on_action_requiring_login(self) -> None:
        """
        Indicate that a user needs to login to perform the specified action.
        """
        error = _("You must sign in to perform this action.")
        self.gui.update_error_status(error)

    def authenticated(self) -> bool:
        """
        Return a boolean indication that the connection to the API is
        authenticated.
        """
        return bool(self.api and self.api.token is not None)

    def get_last_sync(self):  # type: ignore[no-untyped-def]
        """
        Returns the time of last synchronisation with the remote SD server.
        """
        try:
            with open(self.last_sync_filepath) as f:
                return arrow.get(f.read())
        except Exception:
            return None

    def on_sync_started(self) -> None:
        self.sync_started.emit(datetime.utcnow())

    def on_sync_success(self) -> None:
        """
        Called when synchronization of data via the API queue succeeds.

            * Set last sync flag
            * Download new messages and replies
            * Update missing files so that they can be re-downloaded
            * Update authenticated user if name changed
            * Resume queues if they were paused because of a network error since syncing was
              successful
        """
        with open(self.last_sync_filepath, "w") as f:
            f.write(arrow.now().format())
        self.show_last_sync()

        missing_files = storage.update_missing_files(self.data_dir, self.session)
        for missed_file in missing_files:
            self.file_missing.emit(missed_file.source.uuid, missed_file.uuid, str(missed_file))
        self.update_sources()
        self.gui.refresh_current_source_conversation()
        self.download_new_messages()
        self.download_new_replies()
        self.update_failed_replies()
        self.sync_succeeded.emit()

        try:
            if (
                self.authenticated_user
                and self.api
                and (
                    self.authenticated_user.username != self.api.username
                    or self.authenticated_user.firstname != self.api.first_name
                    or self.authenticated_user.lastname != self.api.last_name
                )
            ):
                self.update_authenticated_user.emit(self.authenticated_user)
        except sqlalchemy.orm.exc.ObjectDeletedError:
            self._close_client_session()

        self.resume_queues()

    def on_sync_failure(self, result: Exception) -> None:
        """
        Called when synchronization of data via the API fails after a background sync. If the reason
        a sync fails is ApiInaccessibleError then we need to log the user out for security reasons
        and show them the login window in order to get a new token.
        """
        logger.warning("sync failure")
        logger.debug(f"sync failure: {result}")

        if isinstance(result, ApiInaccessibleError):
            # Don't show login window if the user is already logged out
            if not self.is_authenticated or not self.api:
                return

            self._close_client_session()
        elif isinstance(result, RequestTimeoutError | ServerConnectionError):
            self.gui.update_error_status(
                _("The SecureDrop server cannot be reached. Trying to reconnect..."), duration=0
            )

    def _close_client_session(self) -> None:
        self.invalidate_token()
        self.logout()
        self.gui.show_login(error=_("Your session expired. Please log in again."))

    def show_last_sync(self) -> None:
        """
        Updates the UI to show human time of last sync.
        """
        self.gui.show_last_sync(self.get_last_sync())

    def update_sources(self) -> None:
        """
        Display the updated list of sources with those found in local storage.
        """
        sources = list(storage.get_local_sources(self.session))
        self.gui.show_sources(sources)

    def mark_seen(self, source: db.Source) -> None:
        """
        Mark all unseen conversation items of the supplied source as seen by the current
        authenticated user.
        """
        try:
            # If user is logged out then just return
            if not self.authenticated_user:
                return

            # Prepare the lists of uuids to mark as seen by the current user. Continue to process
            # the next item if the source conversation item has already been seen by the current
            # user or if it no longer exists (individual conversation items can be deleted via the
            # web journalist interface).
            current_user_id = self.authenticated_user.id
            files = []  # type: list[str]
            messages = []  # type: list[str]
            replies = []  # type: list[str]
            source_items = source.collection
            for item in source_items:
                try:
                    if item.seen_by(current_user_id):
                        continue

                    if isinstance(item, db.File):
                        files.append(item.uuid)
                    elif isinstance(item, db.Message):
                        messages.append(item.uuid)
                    elif isinstance(item, db.Reply):
                        replies.append(item.uuid)
                except sqlalchemy.exc.InvalidRequestError as e:
                    logger.debug(e)
                    continue

            # If there's nothing to be marked as seen, just return.
            if not files and not messages and not replies:
                return

            job = SeenJob(files, messages, replies)
            job.success_signal.connect(self.on_seen_success)
            job.failure_signal.connect(self.on_seen_failure)
            self.add_job.emit(job)
        except sqlalchemy.exc.InvalidRequestError as e:
            logger.debug(e)

    def on_seen_success(self) -> None:
        pass

    def on_seen_failure(self, error: Exception) -> None:
        logger.debug(error)

    def on_update_star_success(self, source_uuid: str) -> None:
        self.star_update_successful.emit(source_uuid)

    def on_update_star_failure(self, error: UpdateStarJobError | UpdateStarJobTimeoutError) -> None:
        if isinstance(error, UpdateStarJobError):
            self.gui.update_error_status(_("Failed to update star."))
            source = self.session.query(db.Source).filter_by(uuid=error.source_uuid).one()
            self.star_update_failed.emit(error.source_uuid, source.is_starred)

    @login_required
    def update_star(self, source_uuid: str, is_starred: bool) -> None:
        """
        Star or unstar.
        """
        job = UpdateStarJob(source_uuid, is_starred)
        job.success_signal.connect(self.on_update_star_success)
        job.failure_signal.connect(self.on_update_star_failure)
        self.add_job.emit(job)

    def logout(self) -> None:
        """
        If the token is not already invalid, make an api call to logout and invalidate the token.
        Then mark all pending draft replies as failed, stop the queues, and show the user as logged
        out in the GUI.
        """

        # clear error status in case queue was paused resulting in a permanent error message
        self.gui.clear_error_status()

        if self.api is not None:
            self.call_api(self.api.logout, self.on_logout_success, self.on_logout_failure)

        self.invalidate_token()

        self.api_sync.stop()
        self.api_job_queue.stop()
        self.gui.logout()

        self.is_authenticated = False

    def invalidate_token(self) -> None:
        self.api = None
        self.authenticated_user = None

    def set_status(self, message: str, duration: int = 5000) -> None:
        """
        Set a textual status message to be displayed to the user for a certain
        duration.
        """
        self.gui.update_activity_status(message, duration)

    @login_required
    def _submit_download_job(
        self, object_type: type[db.Reply] | type[db.Message] | type[db.File], uuid: str
    ) -> None:
        if object_type == db.Reply:
            job: ReplyDownloadJob | MessageDownloadJob | FileDownloadJob = ReplyDownloadJob(
                uuid, self.data_dir, self.gpg
            )
            job.success_signal.connect(self.on_reply_download_success)
            job.failure_signal.connect(self.on_reply_download_failure)
        elif object_type == db.Message:
            job = MessageDownloadJob(uuid, self.data_dir, self.gpg)
            job.success_signal.connect(self.on_message_download_success)
            job.failure_signal.connect(self.on_message_download_failure)
        elif object_type == db.File:
            job = FileDownloadJob(uuid, self.data_dir, self.gpg)
            job.success_signal.connect(self.on_file_download_success)
            job.failure_signal.connect(self.on_file_download_failure)

        self.add_job.emit(job)

    def download_new_messages(self) -> None:
        new_messages = storage.find_new_messages(self.session)

        for message in new_messages:
            if message.download_error:
                logger.info(
                    f"Download of message {message.uuid} failed since client start; not retrying."
                )
            else:
                self._submit_download_job(type(message), message.uuid)

    def on_message_download_success(self, uuid: str) -> None:
        """
        Called when a message has downloaded.
        """
        self.session.commit()  # Needed to flush stale data.
        message = storage.get_message(self.session, uuid)
        if message:
            self.message_ready.emit(message.source.uuid, message.uuid, message.content)
        else:
            logger.error("Failed to find message uuid in database")
            logger.debug(f"Message {uuid} missing from database but download successful")

    def on_message_download_failure(self, exception: Exception) -> None:
        """
        Called when a message fails to download.
        """
        if isinstance(exception, DownloadChecksumMismatchException):
            # Keep resubmitting the job if the download is corrupted.
            logger.warning(f"Failure due to checksum mismatch, retrying {exception.uuid}")
            self._submit_download_job(exception.object_type, exception.uuid)

        self.session.commit()
        if isinstance(exception, DownloadException):
            message = storage.get_message(self.session, exception.uuid)
            if message:
                self.message_download_failed.emit(message.source.uuid, message.uuid, str(message))
            else:
                logger.warning("Message download failure for uuid not in database.")
                logger.debug(f"Message {exception.uuid} missing from database, was it deleted?")
        else:
            logger.error(f"Unexpected exception: {type(exception)}")
            logger.debug(f"Unexpected exception: {exception}")

    def download_new_replies(self) -> None:
        replies = storage.find_new_replies(self.session)
        for reply in replies:
            if reply.download_error:
                logger.info(
                    f"Download of reply {reply.uuid} failed since client start; not retrying."
                )
            else:
                self._submit_download_job(type(reply), reply.uuid)

    def on_reply_download_success(self, uuid: str) -> None:
        """
        Called when a reply has downloaded.
        """
        self.session.commit()  # Needed to flush stale data.
        reply = storage.get_reply(self.session, uuid)
        if reply:
            self.reply_ready.emit(reply.source.uuid, reply.uuid, reply.content)
        else:
            logger.error("Reply downloaded but reply uuid missing from database")
            logger.debug(f"Reply {uuid} downloaded but uuid missing from database")

    def on_reply_download_failure(self, exception: Exception) -> None:
        """
        Called when a reply fails to download.
        """
        if isinstance(exception, DownloadChecksumMismatchException):
            # Keep resubmitting the job if the download is corrupted.
            logger.warning(f"Failure due to checksum mismatch, retrying {exception.uuid}")
            self._submit_download_job(exception.object_type, exception.uuid)

        self.session.commit()
        if isinstance(exception, DownloadException):
            reply = storage.get_reply(self.session, exception.uuid)
            if reply:
                self.reply_download_failed.emit(reply.source.uuid, reply.uuid, str(reply))
            else:
                # Not necessarily an error, it may have been deleted. Warn.
                logger.warning("Reply download failure for uuid not in database")
                logger.debug(f"Reply {exception.uuid} not found in database")
        else:
            logger.error(f"Unexpected exception: {type(exception)}")
            logger.debug(f"Unexpected exception: {exception}")

    def downloaded_file_exists(self, file: db.File, silence_errors: bool = False) -> bool:
        """
        Check if the file specified by file_uuid exists. If it doesn't update the local db and
        GUI to show the file as not downloaded.

        Logs are created when files don't exist, assuming that is an error. If that situation
        is expected, such errors can be silenced via the silence_errors option.
        """
        if not os.path.exists(file.location(self.data_dir)):
            if not silence_errors:
                self.gui.update_error_status(
                    _("File does not exist in the data directory. Please try re-downloading.")
                )
                logger.warning(
                    f"Cannot find file in {os.path.dirname(file.filename)}. File does not exist."
                )
            missing_files = storage.update_missing_files(self.data_dir, self.session)
            for f in missing_files:
                self.file_missing.emit(f.source.uuid, f.uuid, str(f))
            return False
        return True

    def on_file_open(self, file: db.File) -> None:
        """
        Open the file specified by file_uuid. If the file is missing, update the db so that
        is_downloaded is set to False.
        """
        logger.info(f'Opening file in "{os.path.dirname(file.location(self.data_dir))}".')

        if not self.downloaded_file_exists(file):
            return

        if not self.qubes:
            return

        command = "qvm-open-in-vm"
        args = ["--view-only", "@dispvm:sd-viewer", file.location(self.data_dir)]
        process = QProcess(self)
        process.start(command, args)

    @login_required
    def on_submission_download(
        self, submission_type: type[db.File] | type[db.Message], submission_uuid: str
    ) -> None:
        """
        Download the file associated with the Submission (which may be a File or Message).
        """
        self._submit_download_job(submission_type, submission_uuid)

    def on_file_download_success(self, uuid: str) -> None:
        """
        Called when a file has downloaded.
        """
        self.session.commit()
        file_obj = storage.get_file(self.session, uuid)
        if not file_obj:
            # This shouldn't happen
            logger.error("File downloaded but uuid missing from database")
            logger.debug(f"File {uuid} downloaded but uuid missing from database")
            return

        file_obj.download_error = None
        storage.update_file_size(uuid, self.data_dir, self.session)
        self._state.record_file_download(state.FileId(uuid))

        self.file_ready.emit(file_obj.source.uuid, uuid, file_obj.filename)

    def on_file_download_failure(self, exception: Exception) -> None:
        """
        Called when a file fails to download.
        """
        # Keep resubmitting the job if the download is corrupted.
        if isinstance(exception, DownloadChecksumMismatchException):
            logger.warning(f"Failure due to checksum mismatch, retrying {exception.uuid}")
            self._submit_download_job(exception.object_type, exception.uuid)
        else:
            if isinstance(exception, DownloadDecryptionException):
                logger.error("Failed to decrypt %s", exception.uuid)
                f = storage.get_file(self.session, exception.uuid)
                if not f:
                    # This isn't necessarily an error; the file may have been deleted
                    # at the server and has been removed from the database.
                    logger.warning("File download failure for uuid not in database.")
                    logger.debug(
                        f"File download failure but uuid {exception.uuid} uuid not in database, "
                        "was it deleted?"
                    )
                    return

                self.file_missing.emit(f.source.uuid, f.uuid, str(f))
            self.gui.update_error_status(_("The file download failed. Please try again."))

    def on_delete_conversation_success(self, uuid: str) -> None:
        """
        If the source collection has been successfully scheduled for deletion on the server, emit a
        signal.
        """
        logger.info("Conversation %s successfully scheduled for deletion at server", uuid)

        # Delete conversation locally to ensure that it does not remain on disk until next sync
        storage.delete_local_conversation_by_source_uuid(self.session, uuid, self.data_dir)
        self.conversation_deletion_successful.emit(uuid, datetime.utcnow())

    def on_delete_conversation_failure(self, e: Exception) -> None:
        if isinstance(e, DeleteConversationJobException):
            error = _("Failed to delete conversation at server")
            logger.debug("Failed to delete conversation %s at server", e.source_uuid)
            self.gui.update_error_status(error)
            self.conversation_deletion_failed.emit(e.source_uuid)

    def on_delete_source_success(self, source_uuid: str) -> None:
        """
        Delete source locally once it has been scheduled for deletion at server, and
        emit a signal.
        """
        logger.info("Source %s successfully scheduled for deletion at server", source_uuid)
        storage.delete_local_source_by_uuid(self.session, source_uuid, self.data_dir)
        self.update_sources()

    def on_delete_source_failure(self, e: Exception) -> None:
        if isinstance(e, DeleteSourceJobException):
            error = _("Failed to delete source at server")
            self.gui.update_error_status(error)
            self.source_deletion_failed.emit(e.source_uuid)

    @login_required
    def delete_sources(self, sources: list[db.Source]) -> None:
        """
        Performs a delete operation on one or more source records.

        This method will submit a job to delete each target source record on
        the server. If a given job succeeds, the success handler will
        synchronize the server records with the local state. If not,
        the failure handler will display an error.
        """
        for source in sources:
            try:
                # Accessing source.uuid requires the source object to be
                # present in the database.
                # To avoid passing and referencing orm objects, a simplified
                # ViewModel layer decoupled from the db that presents data to the API/GUI
                # would be another possibility.
                job = DeleteSourceJob(source.uuid)
            except sqlalchemy.orm.exc.ObjectDeletedError:
                logger.warning("DeleteSourceJob requested but source already deleted")
                return

            job.success_signal.connect(self.on_delete_source_success)
            job.failure_signal.connect(self.on_delete_source_failure)

            self.add_job.emit(job)
            self.source_deleted.emit(source.uuid)

    @login_required
    def delete_conversation(self, source: db.Source) -> None:
        """
        Deletes the content of a source conversation.

        This method will submit a job to delete the content on the
        server. If the job succeeds, the next sync will synchronize
        the server records with the local state. If not, the failure
        handler will display an error.
        """
        job = DeleteConversationJob(source.uuid)
        job.success_signal.connect(self.on_delete_conversation_success)
        job.failure_signal.connect(self.on_delete_conversation_failure)

        self.add_job.emit(job)
        self.conversation_deleted.emit(source.uuid)

    @login_required
    def download_conversation(self, id: state.ConversationId) -> None:
        files = self._state.conversation_files(id)
        file_count = len(files)
        download_count = 0
        for file in files:
            if not file.is_downloaded:
                download_count += 1
                job = FileDownloadJob(str(file.id), self.data_dir, self.gpg)
                job.success_signal.connect(self.on_file_download_success)
                job.failure_signal.connect(self.on_file_download_failure)
                self.add_job.emit(job)
                self.file_download_started.emit(file.id)
        logger.debug(
            f"Downloaded {download_count} files, {file_count - download_count} were already downloaded (total: {file_count} files)"  # noqa: E501
        )

    @login_required
    def send_reply(self, source_uuid: str, reply_uuid: str, message: str) -> None:
        """
        Send a reply to a source.
        """
        # If the user account no longer exists, do not send
        if not self.authenticated_user:
            logger.error(f"Sender of reply {reply_uuid} has been deleted")
            return

        source = self.session.query(db.Source).filter_by(uuid=source_uuid).one_or_none()
        if not source:
            logger.error("Cannot send a reply to a source account that has been deleted")
            self.update_sources()  # Refresh source list to remove deleted source widget
            return

        # Before we send the reply, add the draft to the database with a PENDING
        # reply send status.
        reply_status = (
            self.session.query(db.ReplySendStatus)
            .filter_by(name=db.ReplySendStatusCodes.PENDING.value)
            .one()
        )
        draft_reply = db.DraftReply(
            uuid=reply_uuid,
            timestamp=datetime.utcnow(),
            source_id=source.id,
            journalist_id=self.authenticated_user.id,
            file_counter=source.interaction_count,
            content=message,
            send_status_id=reply_status.id,
        )
        self.session.add(draft_reply)
        self.session.commit()

        job = SendReplyJob(source_uuid, reply_uuid, message, self.gpg)
        job.success_signal.connect(self.on_reply_success)
        job.failure_signal.connect(self.on_reply_failure)

        self.add_job.emit(job)

    def on_reply_success(self, reply_uuid: str) -> None:
        logger.info(f"{reply_uuid} sent successfully")
        self.session.commit()
        reply = storage.get_reply(self.session, reply_uuid)
        if reply:
            self.reply_succeeded.emit(reply.source.uuid, reply_uuid, reply.content)
        else:
            logger.error("Reply uuid not found in database")
            logger.debug(f"Reply {reply_uuid} uuid not found in database")

    def on_reply_failure(self, exception: SendReplyJobError | SendReplyJobTimeoutError) -> None:
        logger.debug(f"{exception.reply_uuid} failed to send")

        # only emit failure signal for non-timeout errors
        if isinstance(exception, SendReplyJobError):
            self.reply_failed.emit(exception.reply_uuid)

    def get_file(self, file_uuid: str) -> db.File | None:
        """
        Wraps storage.py. GUI caller can use this method; internally, prioritize
        storage.get_file.
        """
        file = storage.get_file(self.session, file_uuid)
        if not file:
            # Not necessarily an error
            logger.warning("get_file for uuid not in database")
            logger.debug(f"File {file_uuid} not found in database")
            return None

        self.session.refresh(file)
        return file

    def on_logout_success(self, result: Exception) -> None:
        logging.info("Client logout successful")

    def on_logout_failure(self, result: Exception) -> None:
        logging.info("Client logout failure")

    def update_failed_replies(self) -> None:
        """
        Emit an explicit `reply_failed` signal for each pending reply marked as failed by
        the storage layer rather than the API job responsible for sending it (for example,
        if the application quit mid-job or mid-queue).  Without this signal, the reply
        won't be shown as failed in the GUI until the application is restarted.
        """
        failed_replies = storage.mark_all_pending_drafts_as_failed(self.session)
        for failed_reply in failed_replies:
            self.reply_failed.emit(failed_reply.uuid)

    @pyqtSlot(object)
    def on_receive_selected_sources(self, sources: list[db.Source]) -> None:
        self._selected_sources = sources

    def get_selected_sources(self) -> list[db.Source] | None:
        return self._selected_sources

    def get_source_count(self) -> int:
        """
        Return total sources in local storage.
        """
        return self.session.query(db.Source).count()
