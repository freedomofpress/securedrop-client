from securedrop_export.status import BaseStatus


class Status(BaseStatus):
    NO_DEVICE_DETECTED = "NO_DEVICE_DETECTED"
    INVALID_DEVICE_DETECTED = "INVALID_DEVICE_DETECTED"  # Not encrypted, too many encrypted partitions, too nested partition scheme, etc
    MULTI_DEVICE_DETECTED = "MULTI_DEVICE_DETECTED"  # Not currently supported
    UNKNOWN_DEVICE_DETECTED = "UNKNOWN_DEVICE_DETECTED"  # Badly-formatted USB (or locked VeraCrypt/TC - currently not supported)

    DEVICE_LOCKED = "DEVICE_LOCKED"  # One valid device detected, and it's locked
    DEVICE_WRITABLE = (
        "DEVICE_WRITABLE"  # One valid device detected, and it's unlocked (and mounted)
    )

    ERROR_UNLOCK_LUKS = "ERROR_UNLOCK_LUKS"  # Bad passphrase (LUKS)
    ERROR_UNLOCK_GENERIC = "ERROR_UNLOCK_GENERIC"  # May not be used
    ERROR_MOUNT = "ERROR_MOUNT"  # Unlocked but not mounted

    SUCCESS_EXPORT = "SUCCESS_EXPORT"
    ERROR_EXPORT = "ERROR_EXPORT"  # Could not write to disk

    # Export succeeds but drive was not unmounted because the volume is busy.
    # This could happen if the user has an application using the drive elsewhere
    ERROR_UNMOUNT_VOLUME_BUSY = "ERROR_UNMOUNT_VOLUME_BUSY"

    # Export succeeds but drives were not properly unmounted (generic)
    ERROR_EXPORT_CLEANUP = "ERROR_EXPORT_CLEANUP"

    DEVICE_ERROR = (
        "DEVICE_ERROR"  # Something went wrong while trying to check the device
    )
