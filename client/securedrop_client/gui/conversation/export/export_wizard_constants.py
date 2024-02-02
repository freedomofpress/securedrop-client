from enum import IntEnum
from gettext import gettext as _

from securedrop_client.export_status import ExportStatus

"""
Export wizard page ordering, human-readable status messages
"""


# Sequential list of pages (the order matters)
class Pages(IntEnum):
    PREFLIGHT = 0
    ERROR = 1
    INSERT_USB = 2
    UNLOCK_USB = 3
    EXPORT_DONE = 4


# Human-readable status info
STATUS_MESSAGES = {
    ExportStatus.NO_DEVICE_DETECTED: _("No device detected"),
    ExportStatus.MULTI_DEVICE_DETECTED: _("Too many USBs; please insert one supported device."),
    ExportStatus.INVALID_DEVICE_DETECTED: _(
        "Either the drive is not encrypted or there is something else wrong with it."
    ),
    ExportStatus.DEVICE_WRITABLE: _("The device is ready for export."),
    ExportStatus.DEVICE_LOCKED: _("The device is locked."),
    ExportStatus.ERROR_UNLOCK_LUKS: _("The passphrase provided did not work. Please try again."),
    ExportStatus.ERROR_MOUNT: _("Error mounting drive"),
    ExportStatus.ERROR_EXPORT: _("Error during export"),
    ExportStatus.ERROR_EXPORT_CLEANUP: _(
        "Files were exported succesfully, but the drive could not be unmounted"
    ),
    ExportStatus.SUCCESS_EXPORT: _("Export successful"),
    ExportStatus.DEVICE_ERROR: _(
        "Error encountered with this device. See your administrator for help."
    ),
    ExportStatus.ERROR_MISSING_FILES: _("Files were moved or missing and could not be exported."),
    ExportStatus.CALLED_PROCESS_ERROR: _("Error encountered. Please contact support."),
    ExportStatus.UNEXPECTED_RETURN_STATUS: _("Error encountered. Please contact support."),
}
