import logging

from .cli import CLI
from .status import Status
from .volume import Volume, MountedVolume, EncryptionScheme
from securedrop_export.archive import Archive
from securedrop_export.exceptions import ExportException
from typing import List, Optional, Tuple


logger = logging.getLogger(__name__)


class Service:
    """
    Actions that can be performed against USB device(s).
    This is the "API" portion of the export workflow.
    """

    def __init__(self, submission: Archive, cli: CLI = CLI()):
        self.cli = cli
        self.submission = submission

    def scan_all_devices(self) -> Status:
        """
        Check all connected devices and return current device
        status.
        """
        try:
            status, _ = self._check_volumes(self.cli.get_all_volumes())
            return status

        except ExportException as ex:
            logger.error(ex)
            return Status.DEVICE_ERROR

    def export(self) -> Status:
        """
        Export material to USB drive.
        """
        try:
            volumes = self.cli.get_all_volumes()
            status, target = self._check_volumes(volumes)

            if not target:
                logger.error(f"Could not export, no available volumes ({status.value})")
                return status

            # If it's writable, it's a MountedVolume object
            if status == Status.DEVICE_WRITABLE and isinstance(target, MountedVolume):
                return self._write_to_device(target, self.submission)
            elif status == Status.DEVICE_LOCKED:
                status, unlocked_volume = self._unlock_device(
                    self.submission.encryption_key, target
                )
                if status == Status.DEVICE_WRITABLE and isinstance(
                    target, MountedVolume
                ):
                    return self._write_to_device(target, self.submission)
                else:
                    return status
            else:
                logger.info(f"Could not export, volume check was {status.value}")
                return status

        except ExportException as ex:
            logger.debug(ex)
            status = ex.sdstatus if ex.sdstatus is not None else Status.ERROR_EXPORT
            logger.error(f"Enountered {status.value} while trying to export")
            return status

    def _check_volumes(
        self, all_volumes: List[Volume]
    ) -> Tuple[Status, Optional[Volume]]:
        """
        Check all potentially-compatible export devices (removable,
        single-partition USB devices).
        """
        number_devices = len(all_volumes)
        if number_devices == 0:
            return (Status.NO_DEVICE_DETECTED, None)

        # At some point we could consider returning all devices, so
        # that the user can select their desired target device, but for
        # now, only one attached device is supported.
        elif number_devices > 1:
            return (Status.MULTI_DEVICE_DETECTED, None)
        else:
            target_volume = all_volumes[0]
            if isinstance(target_volume, MountedVolume):
                logger.debug("Device is unlocked and mounted")
                return (Status.DEVICE_WRITABLE, target_volume)
            elif target_volume.encryption is EncryptionScheme.LUKS:
                logger.debug("Device is locked LUKS drive")
                return (Status.DEVICE_LOCKED, target_volume)
            else:
                logger.debug("Device status is unknown")
                # This could be a locked VeraCrypt drive, or it could be an
                # invalid drive (another encryption type).
                # The client has to decide whether or not to try to use it
                # (i.e. by prompting for passphrase) or to error.
                # The simplest implementation will have the client error unless
                # it is supplied with an already-unlocked VeraCrypt drive that
                # it can use; a more sophisticated implementation might allow for
                # a finite number of re-prompts before giving up, in case of
                # user error with typing the password, and would return the volume
                # (eg to print information about which drive failed).
                return (Status.UNKNOWN_DEVICE_DETECTED, target_volume)

    def _unlock_device(
        self, passphrase: str, volume: Volume
    ) -> Tuple[Status, Optional[Volume]]:
        """
        Given provided passphrase, unlock target volume.
        """
        if volume:
            if volume.encryption is EncryptionScheme.LUKS:
                try:
                    logger.info("Unlocking LUKS drive")
                    volume = self.cli.unlock_luks_volume(volume, passphrase)
                    if volume.unlocked:
                        logger.debug("Volume unlocked, attempt to mount")
                        # Returns MountedVolume or errors
                        return (Status.DEVICE_WRITABLE, self.cli.mount_volume(volume))
                except ExportException as ex:
                    logger.error(ex)

                return (Status.ERROR_UNLOCK_LUKS, volume)

            # Try to unlock another drive, opportunistically
            # hoping it is VeraCrypt/TC.
            else:
                try:
                    logger.info(
                        "Encryption scheme is not LUKS. Attempt VeraCrypt unlock."
                    )
                    volume = self.cli.attempt_unlock_veracrypt(volume, passphrase)

                    if isinstance(volume, MountedVolume):
                        return (Status.DEVICE_WRITABLE, volume)
                    else:
                        # Might be VeraCrypt, might be madness
                        return (Status.ERROR_UNLOCK_GENERIC, volume)
                except ExportException as ex:
                    logger.error(ex)
                    return (Status.ERROR_UNLOCK_GENERIC, volume)

        else:
            # Trying to unlock devices before having an active device
            logger.warning("Tried to unlock_device but no current volume detected.")
            return (Status.NO_DEVICE_DETECTED, None)

    def _write_to_device(self, volume: MountedVolume, data: Archive) -> Status:
        """
        Export data to volume. CLI unmounts and locks volume on completion, even
        if export was unsuccessful.

        Calling method should handle ExportException.
        """
        self.cli.write_data_to_device(data.tmpdir, data.target_dirname, volume)
        return Status.SUCCESS_EXPORT
