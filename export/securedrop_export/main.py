import os
import shutil
import platform
import logging
import sys
from typing import Optional

from securedrop_export.archive import Archive, Metadata
from securedrop_export.command import Command
from securedrop_export.status import BaseStatus
from securedrop_export.directory import safe_mkdir
from securedrop_export.exceptions import ExportException

from securedrop_export.disk import Service as ExportService
from securedrop_export.print import Service as PrintService

from logging.handlers import TimedRotatingFileHandler, SysLogHandler
from securedrop_export import __version__

DEFAULT_HOME = os.path.join(os.path.expanduser("~"), ".securedrop_export")
LOG_DIR_NAME = "logs"
EXPORT_LOG_FILENAME = "export.log"

logger = logging.getLogger(__name__)


class Status(BaseStatus):
    """
    Status values that can occur during initialization.
    """

    ERROR_LOGGING = "ERROR_LOGGING"
    ERROR_GENERIC = "ERROR_GENERIC"
    ERROR_FILE_NOT_FOUND = "ERROR_FILE_NOT_FOUND"


def entrypoint():
    """
    Entrypoint method (Note: a method is required for setuptools).
    Configure logging, extract tarball, and run desired export service,
    exiting with return code 0.

    Non-zero exit values will cause the system to try alternative
    solutions for mimetype handling, which we want to avoid.
    """
    status, submission = None, None

    try:
        _configure_logging()
        logger.info("Starting SecureDrop Export {}".format(__version__))

        data_path = sys.argv[1]

        # Halt if target file is absent
        if not os.path.exists(data_path):
            logger.info("Archive is not found {}.".format(data_path))
            status = Status.ERROR_FILE_NOT_FOUND

        else:
            logger.debug("Extract tarball")
            submission = Archive(data_path).extract_tarball()
            logger.debug("Validate metadata")
            metadata = Metadata(submission.tmpdir).validate()
            logger.info("Archive extraction and metadata validation successful")

            # If all we're doing is starting the vm, we're done; otherwise,
            # run the appropriate print or export routine
            if metadata.command is not Command.START_VM:
                submission.set_metadata(metadata)
                logger.info(f"Start {metadata.command.value} service")
                status = _start_service(submission)

    except ExportException as ex:
        logger.error(f"Encountered exception {ex.sdstatus.value}, exiting")
        logger.error(ex)
        status = ex.sdstatus

    except Exception as exc:
        logger.error("Encountered exception during export, exiting")
        logger.error(exc)
        status = Status.ERROR_GENERIC

    finally:
        _exit_gracefully(submission, status)


def _configure_logging():
    """
    All logging related settings are set up by this function.
    """
    try:
        safe_mkdir(DEFAULT_HOME)
        safe_mkdir(DEFAULT_HOME, LOG_DIR_NAME)

        log_file = os.path.join(DEFAULT_HOME, LOG_DIR_NAME, EXPORT_LOG_FILENAME)

        # set logging format
        log_fmt = (
            "%(asctime)s - %(name)s:%(lineno)d(%(funcName)s) "
            "%(levelname)s: %(message)s"
        )
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
    except Exception as ex:
        raise ExportException(sdstatus=Status.ERROR_LOGGING) from ex


def _start_service(submission: Archive) -> BaseStatus:
    """
    Start print or export service.
    """
    # Print Routines
    if submission.command is Command.PRINT:
        return PrintService(submission).print()
    elif submission.command is Command.PRINTER_PREFLIGHT:
        return PrintService(submission).printer_preflight()
    elif submission.command is Command.PRINTER_TEST:
        return PrintService(submission).printer_test()

    # Export routines
    elif submission.command is Command.EXPORT:
        return ExportService(submission).export()
    elif (
        submission.command is Command.CHECK_USBS
        or submission.command is Command.CHECK_VOLUME
    ):
        return ExportService(submission).scan_all_devices()

    # Unreachable
    raise ExportException(
        f"unreachable: unknown submission.command value: {submission.command}"
    )


def _exit_gracefully(submission: Archive, status: Optional[BaseStatus] = None):
    """
    Write status code, ensure file cleanup, and exit with return code 0.
    Non-zero exit values will cause the system to try alternative
    solutions for mimetype handling, which we want to avoid.
    """
    if status:
        logger.info(f"Exit gracefully with status: {status.value}")
    else:
        logger.info("Exit gracefully (no status code supplied)")
    try:
        # If the file archive was extracted, delete before returning
        if submission and os.path.isdir(submission.tmpdir):
            shutil.rmtree(submission.tmpdir)
        # Do this after deletion to avoid giving the client two error messages in case of the
        # block above failing
        _write_status(status)
    except Exception as ex:
        logger.error("Unhandled exception: {}".format(ex))
        _write_status(Status.ERROR_GENERIC)
    finally:
        # exit with 0 return code otherwise the os will attempt to open
        # the file with another application
        sys.exit(0)


def _write_status(status: Optional[BaseStatus]):
    """
    Write string to stderr.
    """
    if status:
        logger.info(f"Write status {status.value}")
        sys.stderr.write(status.value)
        sys.stderr.write("\n")
    else:
        logger.info("No status value supplied")
