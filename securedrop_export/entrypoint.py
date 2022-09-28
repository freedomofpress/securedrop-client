import logging
import os
import shutil
import sys
import platform

from logging.handlers import TimedRotatingFileHandler, SysLogHandler
from securedrop_export import __version__
from securedrop_export.archive import Archive
from securedrop_export import main
from securedrop_export.utils import safe_mkdir

CONFIG_PATH = "/etc/sd-export-config.json"
DEFAULT_HOME = os.path.join(os.path.expanduser("~"), ".securedrop_export")
LOG_DIR_NAME = "logs"
EXPORT_LOG_FILENAME = "export.log"

logger = logging.getLogger(__name__)


def configure_logging():
    """
    All logging related settings are set up by this function.
    """
    safe_mkdir(DEFAULT_HOME)
    safe_mkdir(DEFAULT_HOME, LOG_DIR_NAME)

    log_file = os.path.join(DEFAULT_HOME, LOG_DIR_NAME, EXPORT_LOG_FILENAME)

    # set logging format
    log_fmt = "%(asctime)s - %(name)s:%(lineno)d(%(funcName)s) " "%(levelname)s: %(message)s"
    formatter = logging.Formatter(log_fmt)

    handler = TimedRotatingFileHandler(log_file)
    handler.setFormatter(formatter)

    # For rsyslog handler
    if platform.system() != "Linux":  # pragma: no cover
        syslog_file = "/var/run/syslog"
    else:
        syslog_file = "/dev/log"

    sysloghandler = SysLogHandler(address=syslog_file)
    sysloghandler.setFormatter(formatter)
    handler.setLevel(logging.DEBUG)

    # set up primary log
    log = logging.getLogger()
    log.setLevel(logging.DEBUG)
    log.addHandler(handler)
    # add the second logger
    log.addHandler(sysloghandler)


def start():
    try:
        configure_logging()
    except Exception:
        msg = "ERROR_LOGGING"
        main._exit_gracefully(None, msg)

    logger.info("Starting SecureDrop Export {}".format(__version__))
    my_sub = Archive(sys.argv[1], CONFIG_PATH)

    try:
        # Halt immediately if target file is absent
        if not os.path.exists(my_sub.archive):
            logger.info("Archive is not found {}.".format(my_sub.archive))
            msg = "ERROR_FILE_NOT_FOUND"
            main._exit_gracefully(my_sub, msg)
        main.__main__(my_sub)
        # Delete extracted achive from tempfile
        shutil.rmtree(my_sub.tmpdir)
    except Exception as e:
        # exit with 0 return code otherwise the os will attempt to open
        # the file with another application
        logger.error(e)
        msg = "ERROR_GENERIC"
        main._exit_gracefully(my_sub, msg)
