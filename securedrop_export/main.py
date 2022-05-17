import logging
import sys

from securedrop_export import export
from securedrop_export.exceptions import Command, ExportStatus, PrintStatus

from securedrop_export.disk.actions import (
    DiskTestAction,
    DiskExportAction,
    USBTestAction,
)

from securedrop_export.disk.service import Service as ExportService
from securedrop_export.print.service import Service as PrintService

logger = logging.getLogger(__name__)


def __main__(submission):
    submission.extract_tarball()

    try:
        submission.archive_metadata = export.Metadata(submission.tmpdir)
    except Exception:
        exit_gracefully(submission, ExportStatus.ERROR_METADATA_PARSING)

    if not submission.archive_metadata.is_valid():
        exit_gracefully(submission, ExportStatus.ERROR_ARCHIVE_METADATA)

    try:
        command = Command.value_of(submission.archive_metadata.export_method)

        if command is Command.START_VM:
            # No further operations
            exit_gracefully(submission, command)
        else:
            status = None
            try:
                if command in Command.printer_actions():
                    service = ExportService(submission)
                    status = service.run(command)

                elif command in Command.export_actions():
                    service = PrintService(submission)
                    status = service.run(command)

            except ExportException as ex:
                if ex.status:
                    status = ex.status

            finally:
                exit_gracefully(submission, status)

    except ValueError:
        # An unsupported command was sent from the calling VM
        logger.error("Unsuported command, exiting")
        exit_gracefully(submission)


def exit_gracefully(submission: SDExport, status: Status=None, e=None):
    """
    Utility to print error messages, mostly used during debugging,
    then exits successfully despite the error. Always exits 0,
    since non-zero exit values will cause system to try alternative
    solutions for mimetype handling, which we want to avoid.
    """
    logger.info("Exiting with message: {}".format(msg))
    if e:
        logger.error("Captured exception output: {}".format(e.output))
    try:
        # If the file archive was extracted, delete before returning
        if os.path.isdir(submission.tmpdir):
            shutil.rmtree(submission.tmpdir)
        # Do this after deletion to avoid giving the client two error messages in case of the
        # block above failing
        write_status(status)
    except Exception as ex:
        logger.error("Unhandled exception: {}".format(ex))
        write_status(ExportStatus.LEGACY_ERROR_GENERIC)
    # exit with 0 return code otherwise the os will attempt to open
    # the file with another application
    sys.exit(0)


def _write_status(self, status: Status):
    """
    Write string to stderr.
    """
    if status:
        sys.stderr.write(status.value)
        sys.stderr.write("\n")
    else:
        logger.info("No status value supplied")
