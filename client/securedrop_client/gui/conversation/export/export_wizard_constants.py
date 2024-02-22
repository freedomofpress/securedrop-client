from enum import IntEnum
from gettext import gettext as _

from securedrop_client.export_status import ExportStatus

"""
Export wizard page ordering, human-readable status messages
"""


# Sequential list of pages (the enum value matters as a ranked ordering.)
# The reason the 'error' page is second is because the other pages have
# validation logic that means they can't be bypassed by QWizard::next.
# When we need to show an error, it's easier to go 'back' to the error
# page and set it to be a FinalPage than it is to try to skip the conditional
# pages. PyQt6 introduces behaviour that may deprecate this requirement.
class Pages(IntEnum):
    PREFLIGHT = 0
    ERROR = 1
    INSERT_USB = 2
    UNLOCK_USB = 3
    EXPORT_DONE = 4


# Human-readable status info
STATUS_MESSAGES = {
    ExportStatus.NO_DEVICE_DETECTED: _("No device detected"),
    ExportStatus.MULTI_DEVICE_DETECTED: _(
        "Too many USB devices detected; please insert one supported device."
    ),
    ExportStatus.INVALID_DEVICE_DETECTED: _(
        "Either the drive is not encrypted or there is something else wrong with it."
        "<br />"
        "If this is a VeraCrypt drive, please unlock it from within `sd-devices`, then try again."
    ),
    ExportStatus.DEVICE_WRITABLE: _("The device is ready for export."),
    ExportStatus.DEVICE_LOCKED: _("The device is locked."),
    ExportStatus.ERROR_UNLOCK_LUKS: _("The passphrase provided did not work. Please try again."),
    ExportStatus.ERROR_MOUNT: _("Error mounting drive"),
    ExportStatus.ERROR_EXPORT: _("Error during export"),
    ExportStatus.ERROR_UNMOUNT_VOLUME_BUSY: _(
        "Files were exported succesfully, but the USB device could not be unmounted."
    ),
    ExportStatus.ERROR_EXPORT_CLEANUP: _(
        "Files were exported succesfully, but some temporary files remain on disk."
        "Reboot to remove them."
    ),
    ExportStatus.SUCCESS_EXPORT: _("Export successful"),
    ExportStatus.DEVICE_ERROR: _(
        "Error encountered with this device. See your administrator for help."
    ),
    ExportStatus.ERROR_MISSING_FILES: _("Files were moved or missing and could not be exported."),
    ExportStatus.CALLED_PROCESS_ERROR: _("Error encountered. Please contact support."),
    ExportStatus.UNEXPECTED_RETURN_STATUS: _("Error encountered. Please contact support."),
}
