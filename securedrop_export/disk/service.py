import logging

from securedrop_export.archive import Archive

from .cli import CLI
from .status import Status
from .volume import Volume, MountedVolume
from securedrop_export.exceptions import ExportException


logger = logging.getLogger(__name__)


class Service:
    """
    Checks that can be performed against the device(s).
    This is the "API" portion of the export workflow.
    """

    def __init__(self, cli: CLI):
        self.cli = cli

    def scan_all_devices(self) -> Status:
        """
        Check all connected devices and return current device
        status.
        """
        try:
            all_devices = self.cli.get_connected_devices()
            number_devices = len(all_devices)

            if number_devices == 0:
                return Status.NO_DEVICE_DETECTED
            elif number_devices > 1:
                return Status.MULTI_DEVICE_DETECTED
            else:
                return self.scan_single_device(all_devices[0])

        except ExportException as ex:
            logger.error(ex)
            return Status.DEVICE_ERROR  # Could not assess devices

    def scan_single_device(self, blkid: str) -> Status:
        """
        Given a string representing a single block device, see if it
        is a suitable export target and return information about its state.
        """
        try:
            target = self.cli.get_partitioned_device(blkid)

            # See if it's a LUKS drive
            if self.cli.is_luks_volume(target):

                # Returns Volume or throws ExportException
                self.volume = self.cli.get_luks_volume(target)

                # See if it's unlocked and mounted
                if isinstance(self.volume, MountedVolume):
                    logger.debug("LUKS device is already mounted")
                    return Status.DEVICE_WRITABLE
                else:
                    # Prompt for passphrase
                    return Status.DEVICE_LOCKED
            else:
                # Might be VeraCrypt, might be madness
                logger.info("LUKS drive not found")

                # Currently we don't support anything other than LUKS.
                # In future, we will support TC/VC volumes as well
                return Status.INVALID_DEVICE_DETECTED

        except ExportException as ex:
            logger.error(ex)
            if ex.sdstatus:
                return ex.sdstatus
            else:
                return Status.DEVICE_ERROR

    def unlock_device(self, passphrase: str, volume: Volume) -> Status:
        """
        Given provided passphrase, unlock target volume. Currently,
        LUKS volumes are supported.
        """
        if volume:
            try:
                self.volume = self.cli.unlock_luks_volume(volume, passphrase)

                if isinstance(volume, MountedVolume):
                    return Status.DEVICE_WRITABLE
                else:
                    return Status.ERROR_UNLOCK_LUKS

            except ExportException as ex:
                logger.error(ex)
                return Status.ERROR_UNLOCK_LUKS
        else:
            # Trying to unlock devices before having an active device
            logger.warning("Tried to unlock_device but no current volume detected.")
            return Status.NO_DEVICE_DETECTED

    def write_to_device(self, volume: MountedVolume, data: Archive) -> Status:
        """
        Export data to volume. CLI unmounts and locks volume on completion, even
        if export was unsuccessful.
        """
        try:
            self.cli.write_data_to_device(data.tmpdir, data.target_dirname, volume)
            return Status.SUCCESS_EXPORT

        except ExportException as ex:
            logger.error(ex)
            if ex.sdstatus:
                return ex.sdstatus
            else:
                return Status.ERROR_EXPORT
