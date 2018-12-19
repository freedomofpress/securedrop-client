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
from PyQt5.QtWidgets import QMainWindow, QWidget, QVBoxLayout, QDesktopWidget, QStatusBar
from securedrop_client import __version__
from securedrop_client.gui.widgets import (ToolBar, MainView, LoginDialog,
                                           ConversationView,
                                           SourceProfileShortWidget)
from securedrop_client.resources import load_icon
from securedrop_client.storage import get_data

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
        self.setWindowTitle(_("SecureDrop Client {}").format(__version__))
        self.setWindowIcon(load_icon(self.icon))
        self.widget = QWidget()
        widget_layout = QVBoxLayout()
        self.widget.setLayout(widget_layout)
        self.tool_bar = ToolBar(self.widget)
        self.main_view = MainView(self.widget)
        self.main_view.source_list.itemSelectionChanged.connect(self.on_source_changed)
        widget_layout.addWidget(self.tool_bar, 1)
        widget_layout.addWidget(self.main_view, 6)
        self.setCentralWidget(self.widget)
        self.current_source = None  # Tracks which source is shown
        self.conversations = {}
        self.show()
        self.autosize_window()

    def setup(self, controller):
        """
        Create references to the controller logic and instantiate the various
        views used in the UI.
        """
        self.controller = controller  # Reference the Client logic instance.
        self.tool_bar.setup(self, controller)
        self.status_bar = QStatusBar(self)
        self.setStatusBar(self.status_bar)
        self.set_status('Started SecureDrop Client. Please sign in.', 20000)
        self.login_dialog = LoginDialog(self)
        self.main_view.setup(self.controller)

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

    def update_error_status(self, error=None):
        """
        Show an error message on the sidebar.
        """
        self.main_view.update_error_status(error)

    def show_sources(self, sources):
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
            self.main_view.status.setText('Last refresh: ' +
                                          updated_on.humanize())
        else:
            self.main_view.status.setText(_('Waiting to refresh...'))

    def set_logged_in_as(self, username):
        """
        Update the UI to show user logged in with username.
        """
        self.tool_bar.set_logged_in_as(username)

    def logout(self):
        """
        Update the UI to show the user is logged out.
        """
        self.tool_bar.set_logged_out()

    def on_source_changed(self):
        """
        React to when the selected source has changed.
        """
        source_item = self.main_view.source_list.currentItem()
        source_widget = self.main_view.source_list.itemWidget(source_item)
        if source_widget:
            self.current_source = source_widget.source
            self.show_conversation_for(self.current_source)

    def add_item_content_or(self, adder, item, default):
        """
        Private helper function to add correct message to conversation widgets
        """
        if item.is_downloaded is False:
            adder(default)
        else:
            adder(get_data(self.sdc_home, item.filename))

    def show_conversation_for(self, source):
        """
        Show conversation of messages and replies between a source and
        journalists.
        """
        conversation = ConversationView(self)
        conversation.setup(self.controller)

        # Display each conversation item in the source collection.
        for conversation_item in source.collection:

            if conversation_item.filename.endswith('msg.gpg'):
                self.add_item_content_or(conversation.add_message,
                                         conversation_item,
                                         "<Message not yet downloaded>")
            elif conversation_item.filename.endswith('reply.gpg'):
                self.add_item_content_or(conversation.add_reply,
                                         conversation_item,
                                         "<Reply not yet downloaded>")
            else:
                conversation.add_file(source, conversation_item)

        container = QWidget()
        layout = QVBoxLayout()
        container.setLayout(layout)
        source_profile = SourceProfileShortWidget(source, self.controller)

        layout.addWidget(source_profile)
        layout.addWidget(conversation)
        self.main_view.update_view(container)

    def set_status(self, message, duration=5000):
        """
        Display a status message to the user. Optionally, supply a duration
        (in milliseconds), the default value being a duration of 5 seconds.
        """
        self.status_bar.showMessage(message, duration)
