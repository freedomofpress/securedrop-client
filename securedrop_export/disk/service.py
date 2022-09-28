import logging
import os
import subprocess
import sys

from typing import List

from securedrop_export.archive import Archive
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
        status = Status.LEGACY_ERROR_GENERIC

        try:
            all_devices = self.cli.get_connected_devices()
            num_devices = len(all_devices)

            if num_devices == 0:
                raise ExportException(sdstatus=Status.LEGACY_USB_NOT_CONNECTED)
            elif num_devices == 1:
                return Status.LEGACY_USB_CONNECTED
            elif num_devices > 1:
                raise ExportException(sdstatus=Status.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED)

        except ExportException as ex:
            # Use legacy status instead of new status values
            raise ExportException(sdstatus=Status.LEGACY_ERROR_GENERIC) from ex


    def check_disk_format(self) -> Status:
        """
        Check if volume is correctly formatted for export.
        """
        try:
            all_devices = self.cli.get_connected_devices()

            if len(all_devices) == 1:
                device = self.cli.get_partitioned_device(all_devices)
                if not self.cli.is_luks_volume(device):
                    raise ExportException(sdstatus=Status.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED)
                # We can support checking if a drive is already unlocked, but for
                # backwards compatibility, this is the only expected status
                # at this stage 
                return Status.LEGACY_USB_ENCRYPTED

        except ExportException as ex:
            # Return legacy status values for now for ongoing client compatibility
            if ex.sdstatus in [s for s in NewStatus]:
                status = self._legacy_status(ex.sdstatus)
                raise ExportException(sdstatus=status)
            elif ex.sdstatus:
                raise
            else:
                raise ExportException(sdstatus=Status.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED)


    def export(self) -> Status:
        """
        Export all files to target device.
        """
        logger.info("Export archive is disk")

        try:
            all_devices = self.cli.get_connected_devices()

            if len(all_devices) == 1:
                device = self.cli.get_partitioned_device(all_devices[0])

                # Decide what kind of volume it is
                if self.cli.is_luks_volume(device):
                    volume = self.cli.get_luks_volume(device)
                    if not volume.writable:
                        unlocked = self.cli.unlock_luks_volume(
                            volume, self.submission.archive_metadata.encryption_key
                        )
                        mounted = self.cli.mount_volume(unlocked)

                    logger.debug(f"Export submission to {mounted.mountpoint}")
                    self.cli.write_data_to_device(self.submission.tmpdir, self.submission.target_dirname, mounted)
                    return Status.SUCCESS_EXPORT

                else:
                    # Another kind of drive: VeraCrypt/TC, or unsupported.
                    # For now this is an error--in future there will be support
                    # for additional encryption formats
                    logger.error(f"Export failed because {device} is not supported")
                    raise ExportException(sdstatus=Status.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED)

        except ExportException as ex:
            # Return legacy status values for now for ongoing client compatibility
            if ex.sdstatus in [s for s in NewStatus]:
                status = self._legacy_status(ex.sdstatus)
                raise ExportException(sdstatus=status)
            elif ex.sdstatus:
                raise
            else:
                raise ExportException(sdstatus=Status.LEGACY_ERROR_GENERIC)


    def _legacy_status(self, status: NewStatus):
        """
        Backwards-compatibility - status values that client (@0.7.0) is expecting.
        """
        if status is NewStatus.ERROR_MOUNT:
            return Status.LEGACY_ERROR_USB_MOUNT
        elif status in [NewStatus.ERROR_EXPORT, NewStatus.ERROR_EXPORT_CLEANUP]:
            return Status.LEGACY_ERROR_USB_WRITE
        elif status in [NewStatus.ERROR_UNLOCK_LUKS, NewStatus.ERROR_UNLOCK_GENERIC]:
            return Status.LEGACY_USB_BAD_PASSPHRASE
        elif status in [NewStatus.INVALID_DEVICE_DETECTED, NewStatus.MULTI_DEVICE_DETECTED]:
            return Status.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED
        else:
            return Status.LEGACY_ERROR_GENERIC
