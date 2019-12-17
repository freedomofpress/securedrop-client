import logging

from securedrop_export import export
from securedrop_export.exceptions import ExportStatus
from securedrop_export.print.actions import PrintExportAction, PrintTestPageAction
from securedrop_export.usb.actions import USBDiskTestAction, USBExportAction, USBTestAction

logger = logging.getLogger(__name__)


def __main__(submission):
    submission.extract_tarball()

    try:
        submission.archive_metadata = export.Metadata(submission.tmpdir)
    except Exception:
        submission.exit_gracefully(ExportStatus.ERROR_METADATA_PARSING.value)

    if not submission.archive_metadata.is_valid():
        submission.exit_gracefully(ExportStatus.ERROR_ARCHIVE_METADATA.value)

    if submission.archive_metadata.export_method == "usb-test":
        action = USBTestAction(submission)
    elif submission.archive_metadata.export_method == "disk":
        action = USBExportAction(submission)
    elif submission.archive_metadata.export_method == "disk-test":
        action = USBDiskTestAction(submission)
    elif submission.archive_metadata.export_method == "printer":
        action = PrintExportAction(submission)
    elif submission.archive_metadata.export_method == "printer-test":
        action = PrintTestPageAction(submission)

    action.run()
