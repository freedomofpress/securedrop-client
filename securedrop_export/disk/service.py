import logging

from securedrop_export.exceptions import ExportException

from .cli import CLI
from .status import Status
from .new_status import Status as NewStatus

logger = logging.getLogger(__name__)


class Service:
    def __init__(self, submission, cli=None):
        self.submission = submission
        self.cli = cli or CLI()

    def check_connected_devices(self) -> Status:
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
            raise ExportException(sdstatus=Status.LEGACY_ERROR_USB_CHECK) from ex

        if num_devices == 0:
            raise ExportException(sdstatus=Status.LEGACY_USB_NOT_CONNECTED)
        elif num_devices == 1:
            return Status.LEGACY_USB_CONNECTED
        elif num_devices > 1:
            raise ExportException(sdstatus=Status.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED)

    def check_disk_format(self) -> Status:
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
                        sdstatus=Status.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED
                    )
                # We can support checking if a drive is already unlocked, but for
                # backwards compatibility, this is the only expected status
                # at this stage
                return Status.LEGACY_USB_ENCRYPTED

        except ExportException as ex:
            logger.error(
                f"Error encountered during disk format check: {ex.sdstatus.value}"
            )
            # Return legacy status values for now for ongoing client compatibility
            if ex.sdstatus in [s for s in NewStatus]:
                status = self._legacy_status(ex.sdstatus)
                raise ExportException(sdstatus=status)
            elif ex.sdstatus:
                raise
            else:
                raise ExportException(sdstatus=Status.LEGACY_USB_DISK_ERROR)

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
                        sdstatus=Status.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED
                    )

        except ExportException as ex:
            logger.error(
                f"Error encountered during disk format check: {ex.sdstatus.value}"
            )
            # Return legacy status values for now for ongoing client compatibility
            if ex.sdstatus in [s for s in NewStatus]:
                status = self._legacy_status(ex.sdstatus)
                raise ExportException(sdstatus=status)
            elif ex.sdstatus:
                raise
            else:
                raise ExportException(sdstatus=Status.LEGACY_ERROR_GENERIC)

    def _legacy_status(self, status: NewStatus) -> Status:
        """
        Backwards-compatibility - status values that client (@0.7.0) is expecting.
        """
        logger.info(f"Convert to legacy: {status.value}")
        if status is NewStatus.ERROR_MOUNT:
            return Status.LEGACY_ERROR_USB_MOUNT
        elif status in [NewStatus.ERROR_EXPORT, NewStatus.ERROR_EXPORT_CLEANUP]:
            return Status.LEGACY_ERROR_USB_WRITE
        elif status in [NewStatus.ERROR_UNLOCK_LUKS, NewStatus.ERROR_UNLOCK_GENERIC]:
            return Status.LEGACY_USB_BAD_PASSPHRASE
        elif status in [
            NewStatus.INVALID_DEVICE_DETECTED,
            NewStatus.MULTI_DEVICE_DETECTED,
        ]:
            return Status.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED
        # The other status values, such as Status.NO_DEVICE_DETECTED, are not returned by the
        # CLI, so we don't need to check for them here
        else:
            return Status.LEGACY_ERROR_GENERIC
