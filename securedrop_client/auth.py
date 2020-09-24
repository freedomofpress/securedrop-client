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
import inspect
import logging
import uuid
from gettext import gettext as _
from typing import Any, Dict, List, Tuple, Type, Union  # noqa: F401

import sdclientapi
from PyQt5.QtCore import QObject, QThread, pyqtSignal
from sdclientapi import RequestTimeoutError, ServerConnectionError

from securedrop_client import db, storage

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
        # Contains active threads calling the API.
        self.api_threads = {}  # type: Dict[str, Dict]
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
            if isinstance(ex, (RequestTimeoutError, ServerConnectionError)):
                self.call_timed_out.emit()

            logger.error(ex)
            self.result = ex
            self.call_failed.emit()
        else:
            self.call_succeeded.emit()


class UserAuth(QObject):
    """
    A signal that emits a signal when the authentication state changes.
    - `True` when the client becomes authenticated
    - `False` when the client becomes unauthenticated
    """

    authentication_state = pyqtSignal(bool, db.User)

    def __init__(self) -> None:
        self._authenticated = False
        self._api = None  # type: sdclientapi.API
        self.user = None  # type: db.User

    @property
    def authenticated(self) -> bool:
        return self._authenticated

    @authenticated.setter
    def authenticated(self, authenticated: bool) -> None:
        if self._authenticated != authenticated:
            self._authenticated = authenticated
            self.authentication_state.emit(authenticated)

    @authenticated.deleter
    def authenticated(self) -> None:
        raise AttributeError("Cannot delete `authenticated`")

    def authenticated(self):
        """
        Return a boolean indication that the connection to the API is
        authenticated.
        """
        return bool(self.api and self.api.token is not None)

    def call_api(
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
        callback with the result. Calls timeout if the timer associated with
        the call emits a timeout signal. Any further arguments are passed to
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

    def completed_api_call(self, thread_id, user_callback):
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

    def invalidate_token(self):
        self.api = None
        self.user = None

    def authenticate(
        self, hostname: str, proxy: bool, username: str, password: str, totp: str, timeout: int = 60
    ):
        """
        Given a username, password and time based one-time-passcode (TOTP), create a new instance
        representing the SecureDrop api and authenticate.

        Default to 60 seconds until we implement a better request timeout strategy. We lower the
        default_request_timeout for Queue API requests in ApiJobQueue in order to display errors
        faster.
        """
        self.api = sdclientapi.API(
            hostname, username, password, totp, proxy, default_request_timeout=timeout
        )
        self.call_api(
            self.api.authenticate, self.on_authenticate_success, self.on_authenticate_failure
        )
        self.show_last_sync_timer.stop()
        self.set_status("")

    def on_authenticate_success(self, result):
        self.authenticated = True
        self.authentication_state.emit(self.authenticated, user)

    def on_authenticate_failure(self, result: Exception) -> None:
        # Failed to authenticate. Reset state with failure message.
        self.invalidate_token()
        error = _(
            "That didn't work. Please check everything and try again.\n"
            "Make sure to use a new two-factor code."
        )
        self.gui.show_login_error(error=error)
        self.api_sync.stop()

    def login(self, username, password, totp):
        self.api = sdclientapi.API(
            self.hostname, username, password, totp, self.proxy, default_request_timeout=60
        )
        self.call_api(
            self.api.authenticate, self.on_authenticate_success, self.on_authenticate_failure
        )

    def authenticated(self):
        """
        Return a boolean indication that the connection to the API is
        authenticated.
        """
        return bool(self.api and self.api.token is not None)

    def logout(self):
        if self.api is not None:
            self.call_api(self.api.logout, self.on_logout_success, self.on_logout_failure)
            self.invalidate_token()

        self.is_authenticated = False

    def on_logout_success(self, result) -> None:
        logging.info("Client logout successful")

    def on_logout_failure(self, result: Exception) -> None:
        logging.info("Client logout failure")
