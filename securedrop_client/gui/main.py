# coding: utf-8

"""
Contains the core UI class for the application. All interactions with the UI
go through an instance of this class.

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
import logging
from gettext import gettext as _
from typing import List, Optional

from PyQt5.QtCore import Qt
from PyQt5.QtGui import QClipboard, QGuiApplication, QIcon, QKeySequence
from PyQt5.QtWidgets import QAction, QApplication, QHBoxLayout, QMainWindow, QVBoxLayout, QWidget

from securedrop_client import __version__, state
from securedrop_client.db import Source, User
from securedrop_client.gui.auth import LoginDialog
from securedrop_client.gui.widgets import LeftPane, MainView, TopPane
from securedrop_client.logic import Controller
from securedrop_client.resources import load_css, load_font, load_icon

logger = logging.getLogger(__name__)


class Window(QMainWindow):
    """
    Represents the application's main window that will contain the UI widgets.
    All interactions with the UI go through the object created by this class.
    """

    icon = "icon.png"

    def __init__(
        self,
        app_state: Optional[state.State] = None,
    ) -> None:
        """
        Create the default start state. The window contains a root widget into
        which is placed:

        * A status bar widget at the top, containing curent user / status
          information.
        * A main-view widget, itself containing a list view for sources and a
          place for details / message contents / forms.
        """
        super().__init__()
        load_font("Montserrat")
        load_font("Source_Sans_Pro")
        self.setStyleSheet(load_css("sdclient.css"))
        self.setWindowTitle(_("SecureDrop Client {}").format(__version__))
        self.setWindowIcon(load_icon(self.icon))

        # Top Pane to display activity and error messages
        self.top_pane = TopPane()

        # Main Pane to display everything else
        self.main_pane = QWidget()
        self.setObjectName("MainWindow")
        layout = QHBoxLayout()
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)
        self.main_pane.setLayout(layout)
        self.left_pane = LeftPane()
        self.main_view = MainView(self.main_pane, app_state)
        layout.addWidget(self.left_pane)
        layout.addWidget(self.main_view)

        # Set the main window's central widget to show Top Pane and Main Pane
        self.central_widget = QWidget()
        central_widget_layout = QVBoxLayout()
        central_widget_layout.setContentsMargins(0, 0, 0, 0)
        central_widget_layout.setSpacing(0)
        self.central_widget.setLayout(central_widget_layout)
        self.setCentralWidget(self.central_widget)
        central_widget_layout.addWidget(self.top_pane)
        central_widget_layout.addWidget(self.main_pane)

        # Dialogs
        self.login_dialog: Optional[LoginDialog] = None

        # Actions
        quit = QAction(_("Quit"), self)
        quit.setIcon(QIcon.fromTheme("application-exit"))
        quit.setShortcut(QKeySequence.Quit)
        quit.triggered.connect(self.close)
        self.addAction(quit)

    def setup(self, controller: Controller) -> None:
        """
        Create references to the controller logic and instantiate the various
        views used in the UI.
        """
        self.controller = controller
        self.top_pane.setup(self.controller)
        self.left_pane.setup(self, self.controller)
        self.main_view.setup(self.controller)
        self.show_login()

    def show_main_window(self, db_user: Optional[User] = None) -> None:
        """
        Show main application window.
        """
        if self.isHidden():
            if not self.controller.qubes:
                self.showMaximized()
            else:
                self.setWindowState(Qt.WindowFullScreen)
                self.show()

        if db_user:
            self.set_logged_in_as(db_user)

    def show_login(self, error: str = "") -> None:
        """
        Show the login form.
        """
        self.login_dialog = LoginDialog(self)

        # Always display the login dialog centered in the screen.
        screen_size = QGuiApplication.primaryScreen().availableGeometry()
        login_dialog_size = self.login_dialog.geometry()
        x_center = int((screen_size.width() - login_dialog_size.width()) / 2)
        y_center = int((screen_size.height() - login_dialog_size.height()) / 2)
        self.login_dialog.move(x_center, y_center)
        self.login_dialog.setup(self.controller)
        self.login_dialog.reset()
        if error:
            self.login_dialog.error(error)
        self.login_dialog.show()

    def show_login_error(self, error: str) -> None:
        """
        Display an error in the login dialog.
        """
        if self.login_dialog and error:
            self.login_dialog.error(error)

    def hide_login(self) -> None:
        """
        Kill the login dialog.
        """
        if self.login_dialog is not None:
            self.login_dialog.accept()
            self.login_dialog = None

    def refresh_current_source_conversation(self) -> None:
        """
        Update the current conversation if the source collection has changed.
        """
        self.main_view.refresh_source_conversations()

    def show_sources(self, sources: List[Source]) -> None:
        """
        Update the left hand sources list in the UI with the passed in list of
        sources.
        """
        self.main_view.show_sources(sources)

    def show_last_sync(self, updated_on):  # type: ignore [no-untyped-def]
        """
        Display a message indicating the time of last sync with the server.
        """
        if updated_on:
            self.update_sync_status(_("Last Refresh: {}").format(updated_on.humanize()))
        else:
            self.update_sync_status(_("Last Refresh: never"))

    def set_logged_in_as(self, db_user: User) -> None:
        """
        Update the UI to show user logged in with username.
        """
        self.left_pane.set_logged_in_as(db_user)
        self.top_pane.set_logged_in()

    def logout(self) -> None:
        """
        Update the UI to show the user is logged out.
        """
        self.left_pane.set_logged_out()
        self.top_pane.set_logged_out()

    def update_sync_status(self, message: str, duration: int = 0) -> None:
        """
        Display an activity status message to the user. Optionally, supply a duration
        (in milliseconds), the default will continuously show the message.
        """
        self.top_pane.update_sync_status(message, duration)

    def update_activity_status(self, message: str, duration: int = 0) -> None:
        """
        Display an activity status message to the user. Optionally, supply a duration
        (in milliseconds), the default will continuously show the message.
        """
        self.top_pane.update_activity_status(message, duration)

    def update_error_status(self, message: str, duration: int = 10000) -> None:
        """
        Display an error status message to the user. Optionally, supply a duration
        (in milliseconds), the default will continuously show the message.
        """
        self.top_pane.update_error_status(message, duration)

    def clear_error_status(self) -> None:
        """
        Clear any message currently in the error status bar.
        """
        self.top_pane.clear_error_status()

    def clear_clipboard(self) -> None:
        """
        Purge any clipboard contents.
        """
        cb = QApplication.clipboard()
        cb.clear()
        cb.clear(QClipboard.Selection)

    def toggle_source_list_actions_enabled(self, enabled: bool):
        self.main_view.toggle_source_list_actions_enabled(enabled)
