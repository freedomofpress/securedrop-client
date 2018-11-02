"""
Contains the core logic for the application in the Client class.

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
import os
import logging
import sdclientapi
import shutil
import arrow
import copy
import uuid
from sqlalchemy import event
from securedrop_client import storage
from securedrop_client import models
from securedrop_client.utils import check_dir_permissions
from securedrop_client.data import Data
from PyQt5.QtCore import QObject, QThread, pyqtSignal, QTimer
from securedrop_client.message_sync import MessageSync


logger = logging.getLogger(__name__)


class APICallRunner(QObject):
    """
    Used to call the SecureDrop API in a non-blocking manner. Will emit a
    call_finished signal when a result becomes known. The caller should manage
    the state of i_timed_out (a flag used to indicate the call to the API has
    timed out).

    See the call_api method of the Client class for how this is
    done (hint: you should be using the call_api method and not directly
    using this class).
    """

    call_finished = pyqtSignal()  # Indicates there is a result.

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
        self.i_timed_out = False

    def call_api(self):
        """
        Call the API. Emit a boolean signal to indicate the outcome of the
        call. Any return value or exception raised is stored in self.result.
        """
        # this blocks
        try:
            self.result = self.api_call(*self.args, **self.kwargs)
        except Exception as ex:
            logger.error(ex)
            self.result = ex

        # by the time we end up here, who knows how long it's taken
        # we may not want to emit this, if there's nothing to catch it
        if self.i_timed_out is False:
            self.call_finished.emit()
        else:
            logger.info("Thread returned from API call, "
                        "but it had timed out.")  # pragma: no cover


class Client(QObject):
    """
    Represents the logic for the secure drop client application. In an MVC
    application, this is the controller.
    """

    def __init__(self, hostname, gui, session,
                 home: str, proxy: bool = True) -> None:
        """
        The hostname, gui and session objects are used to coordinate with the
        various other layers of the application: the location of the SecureDrop
        proxy, the user interface and SqlAlchemy local storage respectively.
        """

        check_dir_permissions(home)

        super().__init__()
        self.hostname = hostname  # Location of the SecureDrop server.
        self.gui = gui  # Reference to the UI window.
        self.api = None  # Reference to the API for secure drop proxy.
        self.session = session  # Reference to the SqlAlchemy session.
        self.message_thread = None # A thread responsible for fetching messages
        self.home = home # used for finding DB in sync thread
        self.api_threads = {}  # Contains active threads calling the API.
        self.sync_flag = os.path.join(home, 'sync_flag')
        self.home = home  # The "home" directory for client files.
        self.data_dir = os.path.join(self.home, 'data')  # File data.
        self.timer = None  # call timeout timer
        self.proxy = proxy

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
        # If possible, update the UI with available sources.
        self.update_sources()
        # Show the login dialog.
        self.gui.show_login()
        # Create a timer to check for sync status every 30 seconds.
        self.sync_timer = QTimer()
        self.sync_timer.timeout.connect(self.update_sync)
        self.sync_timer.start(30000)
        # Automagically sync with the API every 5 minutes.
        self.sync_update = QTimer()
        self.sync_update.timeout.connect(self.sync_api)
        self.sync_update.start(1000 * 60 * 5)  # every 5 minutes.

        event.listen(models.Submission, 'load', self.on_object_loaded)
        event.listen(models.Submission, 'init', self.on_object_instantiated)

    def on_object_instantiated(self, target, args, kwargs):
        target.data = Data(self.data_dir)

    def on_object_loaded(self, target, context):
        target.data = Data(self.data_dir)


    def call_api(self, function, callback, timeout, *args, current_object=None,
                 **kwargs):
        """
        Calls the function in a non-blocking manner. Upon completion calls the
        callback with the result. Calls timeout if the timer associated with
        the call emits a timeout signal. Any further arguments are passed to
        the function to be called.
        """
        new_thread_id = str(uuid.uuid4())  # Uniquely id the new thread.
        new_timer = QTimer()
        new_timer.setSingleShot(True)
        new_timer.start(20000)

        new_api_thread = QThread(self.gui)
        new_api_runner = APICallRunner(function, current_object, *args,
                                       **kwargs)
        new_api_runner.moveToThread(new_api_thread)
        # handle completed call: copy response data, reset the
        # client, give the user-provided callback the response
        # data
        new_api_runner.call_finished.connect(
            lambda: self.completed_api_call(new_thread_id, callback))
        # we've started a timer. when that hits zero, call our
        # timeout function
        new_timer.timeout.connect(
            lambda: self.timeout_cleanup(new_thread_id, timeout))
        # when the thread starts, we want to run `call_api` on `api_runner`
        new_api_thread.started.connect(new_api_runner.call_api)
        # Add the thread related objects to the api_threads dictionary.
        self.api_threads[new_thread_id] = {
            'thread': new_api_thread,
            'runner': new_api_runner,
            'timer': new_timer,
        }
        # Start the thread and related activity.
        new_api_thread.start()

    def clean_thread(self, thread_id):
        """
        Clean up the identified thread's state after an API call.
        """
        if thread_id in self.api_threads:
            timer = self.api_threads[thread_id]['timer']
            timer.disconnect()
            del(self.api_threads[thread_id])

    def completed_api_call(self, thread_id, user_callback):
        """
        Manage a completed API call. The actual result *may* be an exception or
        error result from the API. It's up to the handler (user_callback) to
        handle these potential states.
        """
        logger.info("Completed API call. Cleaning up and running callback.")
        if thread_id in self.api_threads:
            thread_info = self.api_threads[thread_id]
            runner = thread_info['runner']
            timer = thread_info['timer']
            timer.stop()
            result_data = runner.result
            # The callback may or may not have an associated current_object
            if runner.current_object:
                current_object = runner.current_object
            else:
                current_object = None
            self.clean_thread(thread_id)
            if current_object:
                user_callback(result_data, current_object=current_object)
            else:
                user_callback(result_data)



    def start_message_thread(self):
        """
        Starts the message-fetching thread in the background.
        """
        if not self.message_thread:
            self.message_thread = QThread()
            self.message_sync = MessageSync(self.api, self.home)
            self.message_sync.moveToThread(self.message_thread)
            self.message_thread.started.connect(self.message_sync.run)
            self.message_thread.start()

    def timeout_cleanup(self, thread_id, user_callback):
        """
        Clean up after the referenced thread has timed-out by setting some
        flags and calling the passed user_callback.
        """
        logger.info("API call timed out. Cleaning up and running "
                    "timeout callback.")
        if thread_id in self.api_threads:
            runner = self.api_threads[thread_id]['runner']
            runner.i_timed_out = True
            if runner.current_object:
                current_object = runner.current_object
            else:
                current_object = None
            self.clean_thread(thread_id)
            if current_object:
                user_callback(current_object=current_object)
            else:
                user_callback()

    def login(self, username, password, totp):
        """
        Given a username, password and time based one-time-passcode (TOTP),
        create a new instance representing the SecureDrop api and authenticate.
        """
        self.api = sdclientapi.API(self.hostname, username,
                                   password, totp, self.proxy)
        self.call_api(self.api.authenticate, self.on_authenticate,
                      self.on_login_timeout)

    def on_authenticate(self, result):
        """
        Handles the result of an authentication call against the API.
        """
        if isinstance(result, bool) and result:
            # It worked! Sync with the API and update the UI.
            self.gui.hide_login()
            self.sync_api()
            self.gui.set_logged_in_as(self.api.username)
            self.start_message_thread()
            # Clear the sidebar error status bar if a message was shown
            # to the user indicating they should log in.
            self.gui.update_error_status("")
        else:
            # Failed to authenticate. Reset state with failure message.
            self.api = None
            error = _('There was a problem signing in. '
                      'Please verify your credentials and try again.')
            self.gui.show_login_error(error=error)

    def on_login_timeout(self):
        """
        Reset the form and indicate the error.
        """

        self.api = None
        error = _('The connection to the SecureDrop server timed out. '
                  'Please try again.')
        self.gui.show_login_error(error=error)

    def on_sync_timeout(self):
        """
        Indicate that a sync failed.

        TODO: We don't really want to alert in the error bar _every time_
        this happens. Instead, we should do something like: alert if there
        have been many timeouts in a row.
        """

        error = _('The connection to the SecureDrop server timed out. '
                  'Please try again.')
        self.gui.update_error_status(error=error)

    def on_action_requiring_login(self):
        """
        Indicate that a user needs to login to perform the specified action.
        """
        error = _('You must sign in to perform this action.')
        self.gui.update_error_status(error)

    def on_sidebar_action_timeout(self):
        """
        Indicate that a timeout occurred for an action occuring in the left
        sidebar.
        """
        error = _('The connection to the SecureDrop server timed out. '
                  'Please try again.')
        self.gui.update_error_status(error)

    def authenticated(self):
        """
        Return a boolean indication that the connection to the API is
        authenticated.
        """
        return bool(self.api and self.api.token['token'])

    def sync_api(self):
        """
        Grab data from the remote SecureDrop API in a non-blocking manner.
        """
        logger.debug("In sync_api on thread {}".format(
            self.thread().currentThreadId()))

        if self.authenticated():
            logger.debug("You are authenticated, going to make your call")
            self.call_api(storage.get_remote_data, self.on_synced,
                          self.on_sync_timeout, self.api)
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

    def on_synced(self, result):
        """
        Called when syncronisation of data via the API is complete.
        """
        if isinstance(result, tuple):
            remote_sources, remote_submissions, remote_replies = \
                result

            storage.update_local_storage(self.session, remote_sources,
                                         remote_submissions,
                                         remote_replies)

            # Set last sync flag.
            with open(self.sync_flag, 'w') as f:
                f.write(arrow.now().format())
            # TODO: show something in the conversation view?
            # self.gui.show_conversation_for()
        else:
            # How to handle a failure? Exceptions are already logged. Perhaps
            # a message in the UI?
            pass

        self.update_sources()

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
        self.gui.show_sources(sources)
        self.update_sync()

    def on_update_star_complete(self, result):
        """
        After we star or unstar a source, we should sync the API
        such that the local database is updated.

        TODO: Improve the push to server sync logic.
        """
        if isinstance(result, bool) and result:  # result may be an exception.
            self.sync_api()  # Syncing the API also updates the source list UI
            self.gui.update_error_status("")
        else:
            # Here we need some kind of retry logic.
            logging.info("failed to push change to server")
            error = _('Failed to apply change.')
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
            self.gui.update_error_status("")

        source_sdk_object = sdclientapi.Source(uuid=source_db_object.uuid)

        if source_db_object.is_starred:
            self.call_api(self.api.remove_star, self.on_update_star_complete,
                          self.on_sidebar_action_timeout, source_sdk_object)
        else:
            self.call_api(self.api.add_star, self.on_update_star_complete,
                          self.on_sidebar_action_timeout, source_sdk_object)

    def logout(self):
        """
        Reset the API object and force the UI to update into a logged out
        state.
        """
        self.api = None
        # self.stop_message_thread()
        self.gui.logout()

    def set_status(self, message, duration=5000):
        """
        Set a textual status message to be displayed to the user for a certain
        duration.
        """
        self.gui.set_status(message, duration)

    def on_file_click(self, source_db_object, message):
        """
        Download the file associated with the associated message (which may
        be a Submission or Reply).
        """
        if isinstance(message, models.Submission):
            # Handle submissions.
            func = self.api.download_submission
            sdk_object = sdclientapi.Submission(uuid=message.uuid)
            sdk_object.filename = message.filename
            sdk_object.source_uuid = source_db_object.uuid
        elif isinstance(message, models.Reply):
            # Handle journalist's replies.
            func = self.api.download_reply
            sdk_object = sdclientapi.Reply(uuid=message.uuid)
            sdk_object.filename = message.filename
            sdk_object.source_uuid = source_db_object.uuid
        self.set_status(_('Downloading {}'.format(sdk_object.filename)))
        self.call_api(func, self.on_file_download,
                      self.on_download_timeout, sdk_object, self.data_dir,
                      current_object=message)

    def on_file_download(self, result, current_object):
        """
        Called when a file has downloaded. Cause a refresh to the conversation
        view to display the contents of the new file.
        """
        file_uuid = current_object.uuid
        server_filename = current_object.filename
        if isinstance(result, tuple):
            sha256sum, filename = result
            # The filename contains the location where the file has been
            # stored. On non-Qubes OSes, this will be the data directory.
            # On Qubes OS, this will a ~/QubesIncoming directory. In case
            # we are on Qubes, we should move the file to the data directory
            # and name it the same as the server (e.g. spotless-tater-msg.gpg).
            shutil.move(filename, os.path.join(self.data_dir, server_filename))
            storage.mark_file_as_downloaded(file_uuid, self.session)

            # Refresh the current source conversation, bearing in mind
            # that the user may have navigated to another source.
            self.gui.show_conversation_for(self.gui.current_source)
            self.set_status(
                'Finished downloading {}'.format(current_object.filename))
        else:
            # Update the UI in some way to indicate a failure state.
            self.set_status("The file download failed. Please try again.")

    def on_download_timeout(self, current_object):
        """
        Called when downloading a file has timed out.
        """
        # Update the status bar to indicate a failure state.
        self.set_status("The connection to the SecureDrop server timed out. "
                        "Please try again.")
