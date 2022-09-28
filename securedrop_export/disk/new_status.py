from securedrop_export.enums import ExportEnum

class Status(ExportEnum):

    NO_DEVICE_DETECTED = "NO_DEVICE_DETECTED"
    INVALID_DEVICE_DETECTED  = "INVALID_DEVICE_DETECTED"  # Multi partitioned, not encrypted, etc
    MULTI_DEVICE_DETECTED = "MULTI_DEVICE_DETECTED" # Not currently supported

    DEVICE_LOCKED = "DEVICE_LOCKED" # One device detected, and it's locked
    DEVICE_WRITABLE  = "DEVICE_WRITABLE" # One device detected, and it's unlocked (and mounted)

    ERROR_UNLOCK_LUKS = "ERROR_UNLOCK_LUKS"
    ERROR_UNLOCK_GENERIC = "ERROR_UNLOCK_GENERIC"
    ERROR_MOUNT = "ERROR_MOUNT" # Unlocked but not mounted

    SUCCESS_EXPORT = "SUCCESS_EXPORT"
    ERROR_EXPORT = "ERROR_EXPORT" # Could not write to disk
    ERROR_EXPORT_CLEANUP = "ERROR_EXPORT_CLEANUP" # If export succeeds but drives were not properly unmounted

    DEVICE_ERROR = "DEVICE_ERROR" # Something went wrong while trying to check the device
