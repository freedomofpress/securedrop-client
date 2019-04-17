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
from typing import List

from PyQt5.QtWidgets import QMainWindow, QWidget, QHBoxLayout, QVBoxLayout, QDesktopWidget, QApplication

from securedrop_client import __version__
from securedrop_client.db import Source
from securedrop_client.storage import source_exists
from securedrop_client.gui.widgets import TopPane, LeftPane, MainView, LoginDialog, \
    SourceConversationWrapper
from securedrop_client.resources import load_icon

logger = logging.getLogger(__name__)


class Window(QMainWindow):
    """
    Represents the application's main window that will contain the UI widgets.
    All interactions with the UI go through the object created by this class.
    """

    icon = 'icon.png'

    def __init__(self, sdc_home: str):
        """
        Create the default start state. The window contains a root widget into
        which is placed:

        * A status bar widget at the top, containing curent user / status
          information.
        * A main-view widget, itself containing a list view for sources and a
          place for details / message contents / forms.
        """
        super().__init__()
        self.sdc_home = sdc_home

    def setup(self, controller):
        """
        Create references to the controller logic and instantiate the various
        views used in the UI.
        """
        self.controller = controller  # Reference the Client logic instance.
        self.show_login()

    def show_main_window(self, username: str) -> None:
        self.setWindowTitle(_("SecureDrop Client {}").format(__version__))
        self.setWindowIcon(load_icon(self.icon))

        self.central_widget = QWidget()
        central_widget_layout = QVBoxLayout()
        central_widget_layout.setContentsMargins(0, 0, 0, 0)
        central_widget_layout.setSpacing(0)
        self.central_widget.setLayout(central_widget_layout)
        self.setCentralWidget(self.central_widget)

        self.top_pane = TopPane()
        central_widget_layout.addWidget(self.top_pane)

        self.widget = QWidget()
        widget_layout = QHBoxLayout()
        widget_layout.setContentsMargins(0, 0, 0, 0)
        widget_layout.setSpacing(0)
        self.widget.setLayout(widget_layout)

        self.left_pane = LeftPane()
        self.main_view = MainView(self.widget)
        self.main_view.source_list.itemSelectionChanged.connect(self.on_source_changed)

        widget_layout.addWidget(self.left_pane, 1)
        widget_layout.addWidget(self.main_view, 8)

        central_widget_layout.addWidget(self.widget)

        # Cache a dict of source.uuid -> SourceConversationWrapper
        # We do this to not create/destroy widgets constantly (because it causes UI "flicker")
        self.conversations = {}

        self.autosize_window()
        self.show()

        self.left_pane.setup(self, self.controller)
        self.top_pane.setup(self.controller)
        self.main_view.source_list.setup(self.controller)

        self.set_logged_in_as(username)

    def autosize_window(self):
        """
        Ensure the application window takes up 100% of the available screen
        (i.e. the whole of the virtualised desktop in Qubes dom)
        """
        screen = QDesktopWidget().screenGeometry()
        self.resize(screen.width(), screen.height())

    def show_login(self):
        """
        Show the login form.
        """
        self.login_dialog = LoginDialog(self)
        self.login_dialog.move(QApplication.desktop().screen().rect().center() - self.rect().center())
        self.login_dialog.setup(self.controller)
        self.login_dialog.reset()
        self.login_dialog.exec()

    def show_login_error(self, error):
        """
        Display an error in the login dialog.
        """
        if self.login_dialog and error:
            self.login_dialog.error(error)

    def hide_login(self):
        """
        Kill the login dialog.
        """
        self.login_dialog.accept()
        self.login_dialog = None

    def show_sources(self, sources: List[Source]):
        """
        Update the left hand sources list in the UI with the passed in list of
        sources.
        """
        self.main_view.source_list.update(sources)

    def show_sync(self, updated_on):
        """
        Display a message indicating the data-sync state.
        """
        if updated_on:
            self.update_activity_status(_('Last refresh: {}').format(updated_on.humanize()))
        else:
            self.update_activity_status(_('Waiting to refresh...'), 5000)

    def set_logged_in_as(self, username):
        """
        Update the UI to show user logged in with username.
        """
        self.left_pane.set_logged_in_as(username)
        self.top_pane.enable_refresh()

    def logout(self):
        """
        Update the UI to show the user is logged out.
        """
        self.left_pane.set_logged_out()
        self.top_pane.disable_refresh()

    def on_source_changed(self):
        """
        React to when the selected source has changed.
        """
        source_item = self.main_view.source_list.currentItem()
        source_widget = self.main_view.source_list.itemWidget(source_item)

        # Show conversation for the currently-selected source if it hasn't been deleted. If the
        # current source no longer exists, clear the conversation for that source.
        if source_widget and source_exists(self.controller.session, source_widget.source.uuid):
            self.show_conversation_for(source_widget.source, self.controller.is_authenticated)
        else:
            self.main_view.clear_conversation()

    def show_conversation_for(self, source: Source, is_authenticated: bool):
        """
        Show conversation of messages and replies between a source and
        journalists.
        """
        conversation_container = self.conversations.get(source.uuid, None)

        if conversation_container is None:
            conversation_container = SourceConversationWrapper(source,
                                                               self.sdc_home,
                                                               self.controller,
                                                               is_authenticated)
            self.conversations[source.uuid] = conversation_container

        self.main_view.set_conversation(conversation_container)

    def update_activity_status(self, message: str, duration=0):
        """
        Display an activity status message to the user. Optionally, supply a duration
        (in milliseconds), the default will continuously show the message.
        """
        self.top_pane.update_activity_status(message, duration)

    def update_error_status(self, message: str, duration=10000):
        """
        Display an error status message to the user. Optionally, supply a duration
        (in milliseconds), the default will continuously show the message.
        """
        self.top_pane.update_error_status(message, duration)

    def clear_error_status(self):
        """
        Clear any message currently in the error status bar.
        """
        self.top_pane.clear_error_status()
