import contextlib
import io
import logging
import os
import platform
import shutil
import sys
from logging.handlers import SysLogHandler, TimedRotatingFileHandler

from securedrop_export import __version__
from securedrop_export.archive import Archive, Metadata
from securedrop_export.command import Command
from securedrop_export.directory import safe_mkdir
from securedrop_export.disk import Service as ExportService
from securedrop_export.exceptions import ExportException
from securedrop_export.print import Service as PrintService
from securedrop_export.status import BaseStatus

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

    The program is called with the archive name as the first argument.
    """
    status, archive = None, None

    try:
        _configure_logging()
        logger.info("Starting SecureDrop Export {}".format(__version__))

        data_path = sys.argv[1]

        # Halt if target file is absent
        if not os.path.exists(data_path):
            logger.error("Archive not found at provided path.")
            logger.debug("Archive missing, path: {}".format(data_path))
            status = Status.ERROR_FILE_NOT_FOUND

        else:
            logger.debug("Extract tarball")
            archive = Archive(data_path).extract_tarball()
            logger.debug("Validate metadata")
            metadata = Metadata(archive.tmpdir).validate()
            logger.info("Archive extraction and metadata validation successful")

            # If all we're doing is starting the vm, we're done; otherwise,
            # run the appropriate print or export routine
            if metadata.command is not Command.START_VM:
                archive.set_metadata(metadata)
                logger.info(f"Start {metadata.command.value} service")
                status = _start_service(archive)
                logger.info(f"Status: {status.value}")

    # A nonzero exit status will cause other programs
    # to try to handle the files, which we don't want.
    except Exception as ex:
        logger.error(ex)
        if isinstance(ex, ExportException):
            logger.error(f"Encountered exception {ex.sdstatus.value}, exiting")
            status = ex.sdstatus
        else:
            logger.error("Encountered exception during export, exiting")
            status = Status.ERROR_GENERIC

    finally:
        _exit_gracefully(archive, status)


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


def _start_service(archive: Archive) -> BaseStatus:
    """
    Start print or export service.
    """
    # Print Routines
    if archive.command is Command.PRINT:
        return PrintService(archive).print()
    elif archive.command is Command.PRINTER_PREFLIGHT:
        return PrintService(archive).printer_preflight()
    elif archive.command is Command.PRINTER_TEST:
        return PrintService(archive).printer_test()

    # Export routines
    elif archive.command is Command.EXPORT:
        return ExportService(archive).export()
    elif (
        archive.command is Command.CHECK_USBS or archive.command is Command.CHECK_VOLUME
    ):
        return ExportService(archive).scan_all_devices()

    # Unreachable
    raise ExportException(
        f"unreachable: unknown submission.command value: {archive.command}"
    )


def _exit_gracefully(archive: Archive, status: BaseStatus):
    """
    Write status code, ensure file cleanup, and exit with return code 0.
    Non-zero exit values will cause the system to try alternative
    solutions for mimetype handling, which we want to avoid.
    """
    try:
        # If the file archive was extracted, delete before returning
        if archive and os.path.isdir(archive.tmpdir):
            shutil.rmtree(archive.tmpdir)
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


def _write_status(status: BaseStatus):
    """
    Write status string to stderr. Flush stderr and stdout before we exit.
    """
    logger.info(f"Write status {status.value}")
    try:
        # First we will log errors from stderr elsewhere
        tmp_stderr = io.StringIO()
        tmp_stdout = io.StringIO()
        with contextlib.redirect_stderr(tmp_stderr), contextlib.redirect_stdout(
            tmp_stdout
        ):
            sys.stderr.flush()
            sys.stdout.flush()
            if len(tmp_stderr.getvalue()) > 0:
                logger.error(f"Error capture: {tmp_stderr.getvalue()}")
            if len(tmp_stdout.getvalue()) > 0:
                logger.info(f"stdout capture: {tmp_stderr.getvalue()}")

        sys.stderr.write(status.value)
        sys.stderr.write("\n")
        sys.stderr.flush()
        sys.stdout.flush()
    except BrokenPipeError:
        devnull = os.open(os.devnull, os.O_WRONLY)
        os.dup2(devnull, sys.stdout.fileno())
        os.dup2(devnull, sys.stderr.fileno())
