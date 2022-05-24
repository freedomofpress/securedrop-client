from enum import Enum


class ExportStatus(Enum):

    # General errors
    ERROR_FILE_NOT_FOUND = "ERROR_FILE_NOT_FOUND"
    ERROR_EXTRACTION = "ERROR_EXTRACTION"
    ERROR_METADATA_PARSING = "ERROR_METADATA_PARSING"
    ERROR_ARCHIVE_METADATA = "ERROR_ARCHIVE_METADATA"
    ERROR_USB_CONFIGURATION = "ERROR_USB_CONFIGURATION"
    ERROR_GENERIC = "ERROR_GENERIC"

    # USB preflight related errors
    USB_CONNECTED = "USB_CONNECTED"
    USB_NOT_CONNECTED = "USB_NOT_CONNECTED"
    ERROR_USB_CHECK = "ERROR_USB_CHECK"

    # USB Disk preflight related errors
    USB_ENCRYPTED = "USB_ENCRYPTED"
    USB_ENCRYPTION_NOT_SUPPORTED = "USB_ENCRYPTION_NOT_SUPPORTED"
    USB_DISK_ERROR = "USB_DISK_ERROR"

    # Printer preflight related errors
    ERROR_MULTIPLE_PRINTERS_FOUND = "ERROR_MULTIPLE_PRINTERS_FOUND"
    ERROR_PRINTER_NOT_FOUND = "ERROR_PRINTER_NOT_FOUND"
    ERROR_PRINTER_NOT_SUPPORTED = "ERROR_PRINTER_NOT_SUPPORTED"
    ERROR_PRINTER_DRIVER_UNAVAILABLE = "ERROR_PRINTER_DRIVER_UNAVAILABLE"
    ERROR_PRINTER_INSTALL = "ERROR_PRINTER_INSTALL"

    # Disk export errors
    USB_BAD_PASSPHRASE = "USB_BAD_PASSPHRASE"
    ERROR_USB_MOUNT = "ERROR_USB_MOUNT"
    ERROR_USB_WRITE = "ERROR_USB_WRITE"

    # Printer export errors
    ERROR_PRINT = "ERROR_PRINT"


class TimeoutException(Exception):
    pass


def handler(signum, frame):
    """
    This is a signal handler used for raising timeouts:
    https://docs.python.org/3/library/signal.html#signal.signal
    """
    raise TimeoutException("Timeout")
