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
import gettext
import locale
import logging
import os
import platform
import signal
import socket
import sys
from argparse import ArgumentParser
from gettext import gettext as _
from logging.handlers import SysLogHandler, TimedRotatingFileHandler
from pathlib import Path
from typing import NewType

from PyQt5.QtCore import Qt, QTimer
from PyQt5.QtWidgets import QApplication, QMessageBox

from securedrop_client import __version__
from securedrop_client.db import make_session_maker
from securedrop_client.gui.main import Window
from securedrop_client.logic import Controller
from securedrop_client.utils import safe_mkdir

DEFAULT_SDC_HOME = "~/.securedrop_client"
ENCODING = "utf-8"
LOGLEVEL = os.environ.get("LOGLEVEL", "info").upper()

LanguageCode = NewType("LanguageCode", str)


def init(sdc_home: Path) -> None:
    safe_mkdir(sdc_home)
    safe_mkdir(sdc_home, "data")


def excepthook(*exc_args):
    """
    This function is called in the event of a catastrophic failure.
    Log exception and exit cleanly.
    """
    logging.error("Unrecoverable error", exc_info=(exc_args))
    sys.__excepthook__(*exc_args)
    print("")  # force terminal prompt on to a new line
    sys.exit(1)


def configure_locale_and_language() -> LanguageCode:
    """Configure locale, language and define location of translation assets."""
    localedir = os.path.abspath(os.path.join(os.path.dirname(__file__), "locale"))
    try:
        # Use the operating system's locale.
        current_locale, encoding = locale.getdefaultlocale()
        # Get the language code.
        if current_locale is None:
            code = LanguageCode("en")
        else:
            code = LanguageCode(current_locale[:2])
    except ValueError:  # pragma: no cover
        code = LanguageCode("en")  # pragma: no cover
    gettext.bindtextdomain("messages", localedir=localedir)
    gettext.textdomain("messages")
    return code


def configure_logging(sdc_home: Path) -> None:
    """
    Set up all logging.
    """
    safe_mkdir(sdc_home, "logs")
    log_file = os.path.join(sdc_home, "logs", "client.log")

    # set logging format
    log_fmt = "%(asctime)s - %(name)s:%(lineno)d(%(funcName)s) " "%(levelname)s: %(message)s"
    formatter = logging.Formatter(log_fmt)

    # define log handlers such as for rotating log files
    handler = TimedRotatingFileHandler(
        log_file, when="midnight", backupCount=5, delay=False, encoding=ENCODING
    )
    handler.setFormatter(formatter)

    # For rsyslog handler
    if platform.system() != "Linux":  # pragma: no cover
        syslog_file = "/var/run/syslog"
    else:
        syslog_file = "/dev/log"

    sysloghandler = SysLogHandler(address=syslog_file)
    sysloghandler.setFormatter(formatter)

    # set up primary log
    log = logging.getLogger()
    log.setLevel(LOGLEVEL)
    log.addHandler(handler)

    # add the secondard logger
    log.addHandler(sysloghandler)

    # override excepthook to capture a log of catastrophic failures.
    sys.excepthook = excepthook


def configure_signal_handlers(app) -> None:
    def signal_handler(*nargs) -> None:
        app.quit()

    for sig in [signal.SIGINT, signal.SIGTERM]:
        signal.signal(sig, signal_handler)


def expand_to_absolute(value: str) -> str:
    """
    Expands a path to the absolute path so users can provide
    arguments in the form ``~/my/dir/``.
    """
    return os.path.abspath(os.path.expanduser(value))


def arg_parser() -> ArgumentParser:
    parser = ArgumentParser("securedrop-client", description="SecureDrop Journalist GUI")
    parser.add_argument(
        "-H",
        "--sdc-home",
        default=DEFAULT_SDC_HOME,
        type=expand_to_absolute,
        help=(
            "SecureDrop Client home directory for storing files and state. "
            "(Default {})".format(DEFAULT_SDC_HOME)
        ),
    )
    parser.add_argument(
        "--no-proxy", action="store_true", help="Use proxy AppVM name to connect to server."
    )
    parser.add_argument(
        "--no-qubes", action="store_true", help="Disable opening submissions in DispVMs"
    )
    return parser


def prevent_second_instance(app: QApplication, unique_name: str) -> None:
    # This function is only necessary on Qubes, so we can skip it on other platforms to help devs
    if platform.system() != "Linux":  # pragma: no cover
        return

    # Null byte triggers abstract namespace
    IDENTIFIER = "\0" + app.applicationName() + unique_name
    ALREADY_BOUND_ERRNO = 98

    app.instance_binding = socket.socket(socket.AF_UNIX, socket.SOCK_DGRAM)
    try:
        app.instance_binding.bind(IDENTIFIER)
    except OSError as e:
        if e.errno == ALREADY_BOUND_ERRNO:
            err_dialog = QMessageBox()
            err_dialog.setText(
                _("{application_name} is already running").format(
                    application_name=app.applicationName()
                )
            )
            err_dialog.exec()
            sys.exit()
        else:
            raise


def start_app(args, qt_args) -> None:
    """
    Create all the top-level assets for the application, set things up and
    run the application. Specific tasks include:

    - set up locale and language.
    - set up logging.
    - create an application object.
    - create a window for the app.
    - create an API connection to the SecureDrop proxy.
    - create a SqlAlchemy session to local storage.
    - configure the client (logic) object.
    - ensure the application is setup in the default safe starting state.
    """
    os.umask(0o077)
    configure_locale_and_language()
    init(args.sdc_home)
    configure_logging(args.sdc_home)
    logging.info("Starting SecureDrop Client {}".format(__version__))

    app = QApplication(qt_args)
    app.setApplicationName("SecureDrop Client")
    app.setDesktopFileName("org.freedomofthepress.securedrop.client")
    app.setApplicationVersion(__version__)
    app.setAttribute(Qt.AA_UseHighDpiPixmaps)

    prevent_second_instance(app, args.sdc_home)

    session_maker = make_session_maker(args.sdc_home)

    gui = Window()

    controller = Controller(
        "http://localhost:8081/",
        gui,
        session_maker,
        args.sdc_home,
        not args.no_proxy,
        not args.no_qubes,
    )
    controller.setup()

    configure_signal_handlers(app)
    timer = QTimer()
    timer.start(500)
    timer.timeout.connect(lambda: None)

    sys.exit(app.exec_())


def run() -> None:
    args, qt_args = arg_parser().parse_known_args()
    # reinsert the program's name
    qt_args.insert(0, "securedrop-client")
    start_app(args, qt_args)
