from enum import Enum


class ExportStatus(Enum):
    """
    All possible strings returned by the qrexec calls to sd-devices. These values come from
    `print/status.py` and `disk/status.py` in `https://github.com/freedomofpress/securedrop-export`
    and must only be changed in coordination with changes released in that repo.
    """

    # Export
    NO_DEVICE_DETECTED = "NO_DEVICE_DETECTED"
    INVALID_DEVICE_DETECTED = "INVALID_DEVICE_DETECTED"  # Multi partitioned, not encrypted, etc
    MULTI_DEVICE_DETECTED = "MULTI_DEVICE_DETECTED"  # Not currently supported
    UNKNOWN_DEVICE_DETECTED = "UNKNOWN_DEVICE_DETECTED"  # Badly-formatted USB or VeraCrypt/TC

    DEVICE_LOCKED = "DEVICE_LOCKED"  # One valid device detected, and it's locked
    DEVICE_WRITABLE = (
        "DEVICE_WRITABLE"  # One valid device detected, and it's unlocked (and mounted)
    )

    ERROR_UNLOCK_LUKS = "ERROR_UNLOCK_LUKS"
    ERROR_UNLOCK_GENERIC = "ERROR_UNLOCK_GENERIC"
    ERROR_MOUNT = "ERROR_MOUNT"  # Unlocked but not mounted

    SUCCESS_EXPORT = "SUCCESS_EXPORT"
    ERROR_EXPORT = "ERROR_EXPORT"  # Could not write to disk

    # Export succeeds but drives were not properly unmounted
    ERROR_EXPORT_CLEANUP = "ERROR_EXPORT_CLEANUP"

    DEVICE_ERROR = "DEVICE_ERROR"  # Something went wrong while trying to check the device

    # Print
    ERROR_MULTIPLE_PRINTERS_FOUND = "ERROR_MULTIPLE_PRINTERS_FOUND"
    ERROR_PRINTER_NOT_FOUND = "ERROR_PRINTER_NOT_FOUND"
    ERROR_PRINTER_NOT_SUPPORTED = "ERROR_PRINTER_NOT_SUPPORTED"
    ERROR_PRINTER_DRIVER_UNAVAILABLE = "ERROR_PRINTER_DRIVER_UNAVAILABLE"
    ERROR_PRINTER_INSTALL = "ERROR_PRINTER_INSTALL"
    ERROR_PRINTER_URI = "ERROR_PRINTER_URI"  # new

    # Print error
    ERROR_PRINT = "ERROR_PRINT"

    # New
    PRINT_PREFLIGHT_SUCCESS = "PRINTER_PREFLIGHT_SUCCESS"
    TEST_SUCCESS = "PRINTER_TEST_SUCCESS"
    PRINT_SUCCESS = "PRINTER_SUCCESS"

    ERROR_UNKNOWN = "ERROR_GENERIC"  # Unknown printer error, backwards-compatible

    # Misc
    CALLED_PROCESS_ERROR = "CALLED_PROCESS_ERROR"
    ERROR_USB_CONFIGURATION = "ERROR_USB_CONFIGURATION"
    UNEXPECTED_RETURN_STATUS = "UNEXPECTED_RETURN_STATUS"
