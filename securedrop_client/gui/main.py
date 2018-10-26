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
from PyQt5.QtWidgets import (QMainWindow, QWidget, QVBoxLayout, QDesktopWidget,
                             QStatusBar)
from PyQt5.QtCore import Qt
from securedrop_client import __version__
from securedrop_client.gui.widgets import (ToolBar, MainView, LoginDialog,
                                           ConversationView)
from securedrop_client.resources import load_icon


logger = logging.getLogger(__name__)


class Window(QMainWindow):
    """
    Represents the application's main window that will contain the UI widgets.
    All interactions with the UI go through the object created by this class.
    """

    icon = 'icon.png'

    def __init__(self):
        """
        Create the default start state. The window contains a root widget into
        which is placed:

        * A status bar widget at the top, containing curent user / status
          information.
        * A main-view widget, itself containing a list view for sources and a
          place for details / message contents / forms.
        """
        super().__init__()
        self.setWindowTitle(_("SecureDrop Client {}").format(__version__))
        self.setWindowIcon(load_icon(self.icon))
        self.widget = QWidget()
        widget_layout = QVBoxLayout()
        self.widget.setLayout(widget_layout)
        self.tool_bar = ToolBar(self.widget)
        self.main_view = MainView(self.widget)
        self.main_view.source_list.itemSelectionChanged.\
            connect(self.on_source_changed)
        widget_layout.addWidget(self.tool_bar, 1)
        widget_layout.addWidget(self.main_view, 6)
        self.setCentralWidget(self.widget)
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
            self.main_view.status.setText('Last Sync: ' +
                                          updated_on.humanize())
        else:
            self.main_view.status.setText(_('Waiting to Synchronize'))

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
            self.show_conversation_for(source_widget.source)

    def show_conversation_for(self, source):
        """
        Show conversation of messages and replies between a source and journalists.
        """
        conversation = ConversationView(self)
        conversation.setup(self.controller)
        conversation.add_message('Source name: {}'.format(
                                 source.journalist_designation))
        
        # Display each conversation item in the source collection.
        for conversation_item in source.collection:
            if conversation_item.filename.endswith('msg.gpg'):
                # TODO: Decrypt and display the message
                pass
            elif conversation_item.filename.endswith('reply.gpg'):
                # TODO: Decrypt and display the reply
                pass
            else:
                conversation.add_file(source, conversation_item)

        conversation.add_message('Hello, hello, is this thing switched on?')
        conversation.add_reply('Yes, I can hear you loud and clear!')
        conversation.add_reply('How can I help?')
        conversation.add_message('I have top secret documents relating to '
                                 'a massive technical scandal at the heart '
                                 ' of the Freedom of the Press Foundation. '
                                 'In a shocking turn of events, it appears '
                                 'they give away all their software for FREE.')
        conversation.add_message("Hello: I’m a nurse at one of the trauma "
                                 "centers in town. We've had many patients in "
                                 "the last several months, all with "
                                 "similar/mysterious respiratory issues. My "
                                 "staff has noticed that most live down-wind "
                                 "from the Dole fields West of 696. Some of "
                                 "the patients say they have complained to "
                                 "local authorities about sewage smells. One "
                                 "said she's spotted a truck spraying a "
                                 "sludge of some kind, on the fields at "
                                 "night. I'm attaching a video from the "
                                 "patient who taped the trucks, and a PDF of "
                                 "redacted police reports that other patients "
                                 "shared. I don’t know if there's much you "
                                 "can do, but if there is I would be happy "
                                 "to help.")
        conversation.add_message("I work at the City Water Department, and a "
                                 "man named Reggie Esters is one of our board "
                                 "directors. I believe Reggie is related to "
                                 "Rep Monica Conyers. He's literally never "
                                 "here, and the resume on file for him makes "
                                 "no sense. I have a hunch he is not in his "
                                 "job legitimately, and think you should look "
                                 "into this. Also: someone I work with heard "
                                 "him on the phone once, talking about his "
                                 "'time' at Jackson—that contradicts his "
                                 "resume. It really seems fishy.")
        conversation.add_reply("THIS IS IT THIS IS THE TAPE EVERYONE'S "
                               "LOOKING FOR!!!")
        conversation.add_reply("Hello: I read your story on Sally Dale, and "
                               "her lawsuit against the St. Joseph's "
                               "Orphanage. My great-aunt was one of the nuns "
                               "there. She is willing to be interviewed, but "
                               "does not want her name, location, or any "
                               "identity details released. She feels "
                               "horrible. She wants the children who survived "
                               "to find peace. Thanks.")
        self.main_view.update_view(conversation)

    def set_status(self, message, duration=5000):
        """
        Display a status message to the user. Optionally, supply a duration
        (in milliseconds), the default value being a duration of 5 seconds.
        """
        self.status_bar.showMessage(message, duration)
