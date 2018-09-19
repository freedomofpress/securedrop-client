"""
SecureDrop client - an easy to use interface for SecureDrop in Qubes.

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
import pathlib
import os
import sys
from PyQt5.QtWidgets import QApplication
from PyQt5.QtCore import Qt
from logging.handlers import TimedRotatingFileHandler
from securedrop_client import __version__
from securedrop_client.gui.main import Window


LOG_DIR = os.path.join(str(pathlib.Path.home()), '.securedrop_client')
LOG_FILE = os.path.join(LOG_DIR, 'securedrop_client.log')
ENCODING = 'utf-8'


def excepthook(*exc_args):
    """
    This function is called in the event of a catastrophic failure.
    Log exception and exit cleanly.
    """
    logging.error('Unrecoverable error', exc_info=(exc_args))
    sys.__excepthook__(*exc_args)
    sys.exit(1)


def configure_logging():
    """
    All logging related settings are set up by this function.
    """
    if not os.path.exists(LOG_DIR):
        os.makedirs(LOG_DIR)
    # set logging format
    log_fmt = ('%(asctime)s - %(name)s:%(lineno)d(%(funcName)s) '
               '%(levelname)s: %(message)s')
    formatter = logging.Formatter(log_fmt)
    # define log handlers such as for rotating log files
    handler = TimedRotatingFileHandler(LOG_FILE, when='midnight',
                                       backupCount=5, delay=0,
                                       encoding=ENCODING)
    handler.setFormatter(formatter)
    handler.setLevel(logging.DEBUG)
    # set up primary log
    log = logging.getLogger()
    log.setLevel(logging.DEBUG)
    log.addHandler(handler)
    # override excepthook to capture a log of catastrophic failures.
    sys.excepthook = excepthook


def run():
    """
    Create all the top-level assets for the application, set things up and
    run the application. Specific tasks include:

    - set up logging.

    ToDo:

    - create an application object.
    - create a window for the app.
    """
    configure_logging()
    logging.info('Starting SecureDrop Client {}'.format(__version__))

    app = QApplication(sys.argv)
    app.setApplicationName('SecureDrop Client')
    app.setDesktopFileName('org.freedomofthepress.securedrop.client')
    app.setApplicationVersion(__version__)
    app.setAttribute(Qt.AA_UseHighDpiPixmaps)
    w = Window()
    w.setup()
    sys.exit(app.exec_())
