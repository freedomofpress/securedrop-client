import logging

from securedrop_export import export
from securedrop_export.exceptions import ExportStatus
from securedrop_export.print.actions import (
    PrintExportAction,
    PrintTestPageAction,
    PrintPreflightAction,
)
from securedrop_export.disk.actions import (
    DiskTestAction,
    DiskExportAction,
    USBTestAction,
)

logger = logging.getLogger(__name__)


def __main__(submission):
    submission.extract_tarball()

    try:
        submission.archive_metadata = export.Metadata(submission.tmpdir)
    except Exception:
        submission.exit_gracefully(ExportStatus.ERROR_METADATA_PARSING.value)

    if not submission.archive_metadata.is_valid():
        submission.exit_gracefully(ExportStatus.ERROR_ARCHIVE_METADATA.value)

    if submission.archive_metadata.export_method == "start-vm":
        submission.exit_gracefully("")

    if submission.archive_metadata.export_method == "usb-test":
        action = USBTestAction(submission)
    elif submission.archive_metadata.export_method == "disk":
        action = DiskExportAction(submission)
    elif submission.archive_metadata.export_method == "disk-test":
        action = DiskTestAction(submission)
    elif submission.archive_metadata.export_method == "printer-preflight":
        action = PrintPreflightAction(submission)
    elif submission.archive_metadata.export_method == "printer":
        action = PrintExportAction(submission)
    elif submission.archive_metadata.export_method == "printer-test":
        action = PrintTestPageAction(submission)

    action.run()
