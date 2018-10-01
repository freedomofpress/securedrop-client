#!/usr/bin/env python3

# The sd-proxy RPC script triggered by qubes RPC.

# This script is executed by `/etc/qubes-rpc/sd-proxy`. It must be
# called with exactly one argument: the path to its config file. See
# the README for configuration options.

import sys
import json
import uuid
import subprocess

from . import proxy
from . import config
from . import callbacks
from . import main


def start():
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
