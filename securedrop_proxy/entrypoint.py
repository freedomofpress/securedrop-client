#!/usr/bin/env python3

# The sd-proxy RPC script triggered by qubes RPC.

# This script is executed by `/etc/qubes-rpc/sd-proxy`. It must be
# called with exactly one argument: the path to its config file. See
# the README for configuration options.

import http
import json
import logging
import os
import sys

from logging.handlers import TimedRotatingFileHandler

from securedrop_proxy import main
from securedrop_proxy import proxy
from securedrop_proxy.version import version


DEFAULT_HOME = os.path.join(os.path.expanduser("~"), ".securedrop_proxy")
LOGLEVEL = os.environ.get("LOGLEVEL", "info").upper()


def start() -> None:
    """
    Set up a new proxy object with an error handler, configuration that we read from  argv[1], and
    the original user request from STDIN.
    """
    try:
        configure_logging()

        logging.debug("Starting SecureDrop Proxy {}".format(version))

        # path to config file must be at argv[1]
        if len(sys.argv) != 2:
            raise ValueError(
                "sd-proxy script not called with path to configuration file"
            )

        # read config. `read_conf` will call `p.err_on_done` if there is a config
        # problem, and will return a Conf object on success.
        conf_path = sys.argv[1]
        # a fresh, new proxy object
        p = proxy.Proxy(conf_path=conf_path)

        # read user request from STDIN
        incoming_lines = []
        for line in sys.stdin:
            incoming_lines.append(line)
        incoming = "\n".join(incoming_lines)

        main.__main__(incoming, p)
    except Exception as e:
        response = {
            "status": http.HTTPStatus.INTERNAL_SERVER_ERROR,
            "body": json.dumps({"error": str(e)}),
        }
        print(json.dumps(response))
        sys.exit(1)


def configure_logging() -> None:
    """
    All logging related settings are set up by this function.
    """
    home = os.getenv("SECUREDROP_HOME", DEFAULT_HOME)
    log_folder = os.path.join(home, "logs")
    if not os.path.exists(log_folder):
        os.makedirs(log_folder)

    log_file = os.path.join(home, "logs", "proxy.log")

    # set logging format
    log_fmt = (
        "%(asctime)s - %(name)s:%(lineno)d(%(funcName)s) %(levelname)s: %(message)s"
    )
    formatter = logging.Formatter(log_fmt)

    # define log handlers such as for rotating log files
    handler = TimedRotatingFileHandler(log_file)
    handler.setFormatter(formatter)
    handler.setLevel(logging.DEBUG)

    # set up primary log
    log = logging.getLogger()
    log.setLevel(LOGLEVEL)
    log.addHandler(handler)
