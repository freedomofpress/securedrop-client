#!/usr/bin/env python3

# The sd-proxy RPC script triggered by qubes RPC.

# This script is executed by `/etc/qubes-rpc/sd-proxy`. It must be
# called with exactly one argument: the path to its config file. See
# the README for configuration options.

import json
import logging
import os
import subprocess
import sys
import uuid

from logging.handlers import TimedRotatingFileHandler

from securedrop_proxy import callbacks
from securedrop_proxy import config
from securedrop_proxy import main
from securedrop_proxy import proxy
from securedrop_proxy.version import version


DEFAULT_HOME = os.path.join(os.path.expanduser("~"), ".securedrop_proxy")


def start():
    '''
    Set up a new proxy object with an error handler, configuration that we read from  argv[1], and
    the original user request from STDIN.
    '''
    try:
        configure_logging()
    except Exception as e:
        print(e)
        return

    logging.info('Starting SecureDrop Proxy {}'.format(version))

    # a fresh, new proxy object
    p = proxy.Proxy()

    # set up an error handler early, so we can use it during
    # configuration, etc
    p.on_done = callbacks.err_on_done

    # path to config file must be at argv[1]
    if len(sys.argv) != 2:
        p.simple_error(
            500, "sd-proxy script not called with path to configuration file"
        )
        p.on_done(p.res)

    # read config. `read_conf` will call `p.on_done` if there is a config
    # problem, and will return a Conf object on success.
    conf_path = sys.argv[1]
    p.conf = config.read_conf(conf_path, p)

    # read user request from STDIN
    incoming = []
    for line in sys.stdin:
        incoming.append(line)
    incoming = "\n".join(incoming)

    main.__main__(incoming, p)


def excepthook(*exc_args):
    '''
    This function is called in the event of a catastrophic failure.
    Log exception and exit cleanly.
    '''
    logging.error('Unrecoverable error', exc_info=(exc_args))
    sys.__excepthook__(*exc_args)
    print('')  # force terminal prompt on to a new line
    sys.exit(1)


def configure_logging() -> None:
    '''
    All logging related settings are set up by this function.
    '''
    log_folder = os.path.join(DEFAULT_HOME, 'logs')
    if not os.path.exists(log_folder):
        os.makedirs(log_folder)

    log_file = os.path.join(DEFAULT_HOME, 'logs', 'proxy.log')

    # set logging format
    log_fmt = ('%(asctime)s - %(name)s:%(lineno)d(%(funcName)s) %(levelname)s: %(message)s')
    formatter = logging.Formatter(log_fmt)

    # define log handlers such as for rotating log files
    handler = TimedRotatingFileHandler(log_file)
    handler.setFormatter(formatter)
    handler.setLevel(logging.DEBUG)

    # set up primary log
    log = logging.getLogger()
    log.setLevel(logging.DEBUG)
    log.addHandler(handler)

    # override excepthook to capture a log of catastrophic failures.
    sys.excepthook = excepthook
