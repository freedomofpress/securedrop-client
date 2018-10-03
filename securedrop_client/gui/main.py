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
from PyQt5.QtWidgets import QMainWindow, QWidget, QVBoxLayout, QDesktopWidget
from PyQt5.QtCore import Qt
from securedrop_client import __version__
from securedrop_client.gui.widgets import ToolBar, MainView, LoginView
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
        self.setWindowFlags(Qt.CustomizeWindowHint)
        widget_layout = QVBoxLayout()
        self.widget.setLayout(widget_layout)
        self.tool_bar = ToolBar(self.widget)
        self.main_view = MainView(self.widget)
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
        self.login_view = LoginView(self, self.controller)

    def autosize_window(self):
        """
        Ensure the application window takes up 100% of the available screen
        (i.e. the whole of the virtualised desktop in Qubes dom)
        """
        screen = QDesktopWidget().screenGeometry()
        self.resize(screen.width(), screen.height())

    def show_login(self, error=None):
        """
        Show the login form. If an error message is passed in, the login
        form will display this too.
        """
        self.login_view.reset()
        if error:
            self.login_view.error(error)
        self.main_view.update_view(self.login_view)

    def show_sources(self, sources):
        """
        Update the left hand sources list in the UI with the passed in list of
        sources.
        """
        self.main_view.source_list.update(sources)
