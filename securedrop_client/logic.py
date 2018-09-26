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
import logging

logger = logging.getLogger(__name__)


class Client:
    """
    Represents the logic for the secure drop client application. In an MVC
    application, this is the controller.
    """

    def __init__(self, gui, api, session):
        """
        The gui, api and session objects are used to coordinate with the
        various other layers of the application: the user interface,
        SecureDrop proxy and SqlAlchemy local storage respectively.
        """
        self.gui = gui  # Reference to the UI window.
        self.api = api  # Reference to the API for secure drop proxy.
        self.session = session  # Reference to the SqlAlchemy session.
        # The gui needs to reference this "controller" layer to call methods
        # triggered by UI events.
        self.gui.controller = self

    def setup(self):
        """
        Setup the application with the default state of:

        * Not logged in.
        * Show most recent state of syncronised sources.
        * Show the login screen.
        """
        self.gui.show_login()
        # TODO: Pass in model classes.
        self.gui.show_sources(["Benign Artichoke", "Last Unicorn",
                               "Jocular Beehive", "Sanitary Lemming",
                               "Spectacular Tuba", ])
