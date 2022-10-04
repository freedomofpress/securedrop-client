from securedrop_export.status import BaseStatus

class Status(BaseStatus):

    LEGACY_ERROR_GENERIC = "ERROR_GENERIC"

    # Legacy USB preflight related
    LEGACY_USB_CONNECTED = "USB_CONNECTED" # Success
    LEGACY_USB_NOT_CONNECTED = "USB_NOT_CONNECTED"
    LEGACY_ERROR_USB_CHECK = "ERROR_USB_CHECK"

    # Legacy USB Disk preflight related errors
    LEGACY_USB_ENCRYPTED = "USB_ENCRYPTED" # Success
    LEGACY_USB_ENCRYPTION_NOT_SUPPORTED = "USB_ENCRYPTION_NOT_SUPPORTED"

    #@todo - this can be raised during disk format check
    LEGACY_USB_DISK_ERROR = "USB_DISK_ERROR"

    # Legacy Disk export errors
    LEGACY_USB_BAD_PASSPHRASE = "USB_BAD_PASSPHRASE"
    LEGACY_ERROR_USB_MOUNT = "ERROR_USB_MOUNT"
    LEGACY_ERROR_USB_WRITE = "ERROR_USB_WRITE"

    # New
    SUCCESS_EXPORT = "SUCCESS_EXPORT"