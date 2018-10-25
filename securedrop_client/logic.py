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
import arrow
from securedrop_client import storage
from securedrop_client import models
from securedrop_client.utils import check_dir_permissions
from PyQt5.QtCore import QObject, QThread, pyqtSignal, QTimer


logger = logging.getLogger(__name__)


class APICallRunner(QObject):
    """
    Used to call the SecureDrop API in a non-blocking manner. Will emit a
    timeout signal after 5 seconds.
    """

    call_finished = pyqtSignal(bool)  # Indicates there is a result.
    timeout = pyqtSignal()  # Indicates there was a timeout.

    def __init__(self, api_call, *args, **kwargs):
        """
        Initialise with the function to call the API and any associated
        args and kwargs.
        """
        super().__init__()
        self.api_call = api_call
        self.args = args
        self.kwargs = kwargs
        self.result = None

    def call_api(self):
        """
        Call the API. Emit a boolean signal to indicate the outcome of the
        call. Timeout signal emitted after 5 seconds. Any return value or
        exception raised is stored in self.result.
        """
        self.timer = QTimer()
        self.timer.timeout.connect(lambda: self.timeout.emit())
        self.timer.setSingleShot(True)
        self.timer.start(5000)
        try:
            logger.info('Calling API with "{}" method'.format(
                        self.api_call.__name__))
            self.result = self.api_call(*self.args, **self.kwargs)
            result_flag = bool(self.result)
        except Exception as ex:
            logger.error(ex)
            self.result = ex
            result_flag = False
        self.call_finished.emit(result_flag)

    def on_cancel_timeout(self):
        """
        Handles a signal to indicate the timer should stop.
        """
        self.timer.stop()


class Client(QObject):
    """
    Represents the logic for the secure drop client application. In an MVC
    application, this is the controller.
    """

    finish_api_call = pyqtSignal()  # Acknowledges reciept of an API call.

    def __init__(self, hostname, gui, session, home: str) -> None:
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
        self.api_thread = None  # Currently active API call thread.
        self.sync_flag = os.path.join(home, 'sync_flag')
        self.home = home  # The "home" directory for client files.
        self.data_dir = os.path.join(self.home, 'data')  # File data.

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

    def call_api(self, function, callback, timeout, *args, **kwargs):
        """
        Calls the function in a non-blocking manner. Upon completion calls the
        callback with the result. Calls timeout if the API call emits a
        timeout signal. Any further arguments are passed to the function to be
        called.
        """
        if not self.api_thread:
            self.api_thread = QThread(self.gui)
            self.api_runner = APICallRunner(function, *args, **kwargs)
            self.api_runner.moveToThread(self.api_thread)
            self.api_runner.call_finished.connect(callback)
            self.api_runner.timeout.connect(timeout)
            self.finish_api_call.connect(self.api_runner.on_cancel_timeout)
            self.api_thread.started.connect(self.api_runner.call_api)
            self.api_thread.finished.connect(self.call_reset)
            self.api_thread.start()

    def call_reset(self):
        """
        Clean up this object's state after an API call.
        """
        if self.api_thread:
            self.finish_api_call.emit()
            self.api_runner = None
            self.api_thread = None

    def login(self, username, password, totp):
        """
        Given a username, password and time based one-time-passcode (TOTP),
        create a new instance representing the SecureDrop api and authenticate.
        """
        self.api = sdclientapi.API(self.hostname, username, password, totp)
        self.call_api(self.api.authenticate, self.on_authenticate,
                      self.on_login_timeout)

    def on_authenticate(self, result):
        """
        Handles the result of an authentication call against the API.
        """
        self.call_reset()
        if result:
            # It worked! Sync with the API and update the UI.
            self.gui.hide_login()
            self.sync_api()
            self.gui.set_logged_in_as(self.api.username)
            # Clear the sidebar error status bar if a message was shown
            # to the user indicating they should log in.
            self.gui.update_error_status("")
        else:
            # Failed to authenticate. Reset state with failure message.
            self.api = None
            error = _('There was a problem logging in. Please try again.')
            self.gui.show_login_error(error=error)

    def on_login_timeout(self):
        """
        Reset the form and indicate the error.
        """
        self.call_reset()
        self.api = None
        error = _('The connection to SecureDrop timed out. Please try again.')
        self.gui.show_login_error(error=error)

    def on_action_requiring_login(self):
        """
        Indicate that a user needs to login to perform the specified action.
        """
        error = _('You must login to perform this action.')
        self.gui.update_error_status(error)

    def on_sidebar_action_timeout(self):
        """
        Indicate that a timeout occurred for an action occuring in the left
        sidebar.
        """
        error = _('The connection to SecureDrop timed out. Please try again.')
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
        if self.authenticated():
            self.call_api(storage.get_remote_data, self.on_synced,
                          self.on_login_timeout, self.api)

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
        if result and isinstance(self.api_runner.result, tuple):
            remote_sources, remote_submissions, remote_replies = \
                self.api_runner.result
            self.call_reset()
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
        self.call_reset()
        if result:
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
        self.call_api(func, self.on_file_download,
                      self.on_download_timeout, sdk_object, self.data_dir)

    def on_file_download(self, result):
        """
        Called when a file has downloaded. Cause a refresh to the conversation
        view to display the contents of the new file.
        """
        sha256sum, filename = self.api_runner.result
        self.call_reset()
        if result:
            storage.mark_file_as_downloaded(os.path.basename(filename), 
                                            self.session)
            # Refresh the conversation with the content of the downloaded file.
        else:
            # Update the UI in some way to indicate a failure state.
            self.set_status("Failed to download file, please try again.")

    def on_download_timeout(self):
        """
        Called when downloading a file has timed out.
        """
        # Update the status bar to indicate a failure state.
        self.set_status("Connection to server timed out, please try again.")
