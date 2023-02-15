import logging

from securedrop_export.exceptions import ExportException

from .cli import CLI
from .legacy_status import Status as LegacyStatus
from .status import Status as Status

logger = logging.getLogger(__name__)


class Service:
    def __init__(self, submission, cli=None):
        self.submission = submission
        self.cli = cli or CLI()

    def check_connected_devices(self) -> LegacyStatus:
        """
        Check if single USB is inserted.
        """
        logger.info("Export archive is usb-test")

        try:
            all_devices = self.cli.get_connected_devices()
            num_devices = len(all_devices)

        except ExportException as ex:
            logger.error(f"Error encountered during USB check: {ex.sdstatus.value}")
            # Use legacy status instead of new status values
            raise ExportException(sdstatus=LegacyStatus.LEGACY_ERROR_USB_CHECK) from ex

        if num_devices == 0:
            raise ExportException(sdstatus=LegacyStatus.LEGACY_USB_NOT_CONNECTED)
        elif num_devices == 1:
            return LegacyStatus.LEGACY_USB_CONNECTED
        elif num_devices > 1:
            raise ExportException(
                sdstatus=LegacyStatus.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED
            )
        else:
            # Unreachable, num_devices is a non-negative integer,
            # and we handled all possible cases already
            raise ValueError(f"unreachable: num_devices is negative: {num_devices}")

    def check_disk_format(self) -> LegacyStatus:
        """
        Check if volume is correctly formatted for export.
        """
        try:
            all_devices = self.cli.get_connected_devices()

            if len(all_devices) == 1:
                device = self.cli.get_partitioned_device(all_devices[0])
                logger.info("Check if LUKS")
                if not self.cli.is_luks_volume(device):
                    raise ExportException(
                        sdstatus=LegacyStatus.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED
                    )
                # We can support checking if a drive is already unlocked, but for
                # backwards compatibility, this is the only expected status
                # at this stage
                return LegacyStatus.LEGACY_USB_ENCRYPTED

        except ExportException as ex:
            logger.error(
                f"Error encountered during disk format check: {ex.sdstatus.value}"
            )
            # Return legacy status values for now for ongoing client compatibility
            if ex.sdstatus in [s for s in Status]:
                status = self._legacy_status(ex.sdstatus)
                raise ExportException(sdstatus=status)
            elif ex.sdstatus:
                raise
            else:
                raise ExportException(sdstatus=LegacyStatus.LEGACY_USB_DISK_ERROR)

    def export(self):
        """
        Export all files to target device.
        """
        logger.info("Export archive is disk")

        try:
            all_devices = self.cli.get_connected_devices()

            if len(all_devices) == 1:
                device = self.cli.get_partitioned_device(all_devices[0])

                # Decide what kind of volume it is
                logger.info("Check if LUKS")
                if self.cli.is_luks_volume(device):
                    volume = self.cli.get_luks_volume(device)
                    logger.info("Check if writable")
                    if not volume.writable:
                        logger.info("Not writable-will try unlocking")
                        volume = self.cli.unlock_luks_volume(
                            volume, self.submission.encryption_key
                        )
                        volume = self.cli.mount_volume(volume)

                    logger.info(f"Export submission to {volume.mountpoint}")
                    self.cli.write_data_to_device(
                        self.submission.tmpdir, self.submission.target_dirname, volume
                    )
                    # This is SUCCESS_EXPORT, but the 0.7.0 client is not expecting
                    # a return status from a successful export operation.
                    # When the client is updated, we will return SUCCESS_EXPORT here.

                else:
                    # Another kind of drive: VeraCrypt/TC, or unsupported.
                    # For now this is an error--in future there will be support
                    # for additional encryption formats
                    logger.error(f"Export failed because {device} is not supported")
                    raise ExportException(
                        sdstatus=LegacyStatus.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED
                    )

        except ExportException as ex:
            logger.error(
                f"Error encountered during disk format check: {ex.sdstatus.value}"
            )
            # Return legacy status values for now for ongoing client compatibility
            if ex.sdstatus in [s for s in Status]:
                status = self._legacy_status(ex.sdstatus)
                raise ExportException(sdstatus=status)
            elif ex.sdstatus:
                raise
            else:
                raise ExportException(sdstatus=LegacyStatus.LEGACY_ERROR_GENERIC)

    def _legacy_status(self, status: Status) -> LegacyStatus:
        """
        Backwards-compatibility - status values that client (@0.7.0) is expecting.
        """
        logger.info(f"Convert to legacy: {status.value}")
        if status is Status.ERROR_MOUNT:
            return LegacyStatus.LEGACY_ERROR_USB_MOUNT
        elif status in [Status.ERROR_EXPORT, Status.ERROR_EXPORT_CLEANUP]:
            return LegacyStatus.LEGACY_ERROR_USB_WRITE
        elif status in [Status.ERROR_UNLOCK_LUKS, Status.ERROR_UNLOCK_GENERIC]:
            return LegacyStatus.LEGACY_USB_BAD_PASSPHRASE
        elif status in [
            Status.INVALID_DEVICE_DETECTED,
            Status.MULTI_DEVICE_DETECTED,
        ]:
            return LegacyStatus.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED
        # The other status values, such as Status.NO_DEVICE_DETECTED, are not returned by the
        # CLI, so we don't need to check for them here
        else:
            return LegacyStatus.LEGACY_ERROR_GENERIC
