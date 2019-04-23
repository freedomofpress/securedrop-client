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
import os
import platform
import signal
import sys
import socket
from argparse import ArgumentParser
from sqlalchemy.orm import sessionmaker
from PyQt5.QtWidgets import QApplication, QMessageBox
from PyQt5.QtCore import Qt, QTimer
from logging.handlers import TimedRotatingFileHandler
from securedrop_client import __version__
from securedrop_client.logic import Controller
from securedrop_client.gui.main import Window
from securedrop_client.resources import load_icon, load_css
from securedrop_client.db import make_engine
from securedrop_client.utils import safe_mkdir

DEFAULT_SDC_HOME = '~/.securedrop_client'
ENCODING = 'utf-8'


def init(sdc_home: str) -> None:
    safe_mkdir(sdc_home)
    safe_mkdir(sdc_home, 'data')


def excepthook(*exc_args):
    """
    This function is called in the event of a catastrophic failure.
    Log exception and exit cleanly.
    """
    logging.error('Unrecoverable error', exc_info=(exc_args))
    sys.__excepthook__(*exc_args)
    print('')  # force terminal prompt on to a new line
    sys.exit(1)


def configure_logging(sdc_home: str) -> None:
    """
    All logging related settings are set up by this function.
    """
    safe_mkdir(sdc_home, 'logs')
    log_file = os.path.join(sdc_home, 'logs', 'client.log')

    # set logging format
    log_fmt = ('%(asctime)s - %(name)s:%(lineno)d(%(funcName)s) '
               '%(levelname)s: %(message)s')
    formatter = logging.Formatter(log_fmt)

    # define log handlers such as for rotating log files
    handler = TimedRotatingFileHandler(log_file, when='midnight',
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


def configure_signal_handlers(app) -> None:
    def signal_handler(*nargs) -> None:
        app.quit()

    for sig in [signal.SIGINT, signal.SIGTERM]:
        signal.signal(sig, signal_handler)


def expand_to_absolute(value: str) -> str:
    '''
    Helper that expands a path to the absolute path so users can provide
    arguments in the form ``~/my/dir/``.
    '''
    return os.path.abspath(os.path.expanduser(value))


def arg_parser() -> ArgumentParser:
    parser = ArgumentParser('securedrop-client',
                            description='SecureDrop Journalist GUI')
    parser.add_argument(
        '-H', '--sdc-home',
        default=DEFAULT_SDC_HOME,
        type=expand_to_absolute,
        help=('SecureDrop Client home directory for storing files and state. '
              '(Default {})'.format(DEFAULT_SDC_HOME)))
    parser.add_argument(
        '--no-proxy', action='store_true',
        help='Use proxy AppVM name to connect to server.')
    return parser


def prevent_second_instance(app: QApplication, unique_name: str) -> None:
    # This function is only necessary on Qubes, so we can skip it on other platforms to help devs
    if platform.system() != 'Linux':  # pragma: no cover
        return

    # Null byte triggers abstract namespace
    IDENTIFIER = '\0' + app.applicationName() + unique_name
    ALREADY_BOUND_ERRNO = 98

    app.instance_binding = socket.socket(socket.AF_UNIX, socket.SOCK_DGRAM)
    try:
        app.instance_binding.bind(IDENTIFIER)
    except OSError as e:
        if e.errno == ALREADY_BOUND_ERRNO:
            err_dialog = QMessageBox()
            err_dialog.setText(app.applicationName() + ' is already running.')
            err_dialog.exec()
            sys.exit()
        else:
            raise


def start_app(args, qt_args) -> None:
    """
    Create all the top-level assets for the application, set things up and
    run the application. Specific tasks include:

    - set up logging.
    - create an application object.
    - create a window for the app.
    - create an API connection to the SecureDrop proxy.
    - create a SqlAlchemy session to local storage.
    - configure the client (logic) object.
    - ensure the application is setup in the default safe starting state.
    """
    init(args.sdc_home)
    configure_logging(args.sdc_home)
    logging.info('Starting SecureDrop Client {}'.format(__version__))

    app = QApplication(qt_args)
    app.setApplicationName('SecureDrop Client')
    app.setDesktopFileName('org.freedomofthepress.securedrop.client')
    app.setApplicationVersion(__version__)
    app.setAttribute(Qt.AA_UseHighDpiPixmaps)

    prevent_second_instance(app, args.sdc_home)

    gui = Window(args.sdc_home)
    app.setWindowIcon(load_icon(gui.icon))
    app.setStyleSheet(load_css('sdclient.css'))

    engine = make_engine(args.sdc_home)
    Session = sessionmaker(bind=engine)
    session = Session()

    controller = Controller("http://localhost:8081/", gui, session,
                            args.sdc_home, not args.no_proxy)
    controller.setup()

    configure_signal_handlers(app)
    timer = QTimer()
    timer.start(500)
    timer.timeout.connect(lambda: None)

    sys.exit(app.exec_())


def run() -> None:
    args, qt_args = arg_parser().parse_known_args()
    # reinsert the program's name
    qt_args.insert(0, 'securedrop-client')
    start_app(args, qt_args)
