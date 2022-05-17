import logging
import os
import subprocess
import sys

from typing import List

from securedrop_export.export import Archive
from securedrop_export.exceptions import ExportException

from .cli import CLI
from .status import Status

logger = logging.getLogger(__name__)


class Service():

    def __init__(self, submission):
        self.submission = submission
        self.cli = CLI()

    def usb_test(self):
        """
        Check if single USB is inserted.
        """
        logger.info("Export archive is usb-test")
        status = Status.LEGACY_ERROR_GENERIC

        try:
            all_devices = self.cli.get_connected_devices()
            num_devices = len(all_devices)

            if num_devices == 0:
                raise ExportException(Status.LEGACY_USB_NOT_CONNECTED)
            elif num_devices == 1:
                status = Status.LEGACY_USB_CONNECTED
            elif num_devices > 1:
                raise ExportException(Status.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED)

        except ExportException:
            raise


    def disk_format_test(self):
        """
        Check if volume is correctly formatted for export.
        """
        try:
            all_devices = self.cli.get_connected_devices()

            if len(all_devices) == 1:
                device = self.cli.get_partitioned_device(all_devices)
                if self.cli.is_luks_volume(device):
                    status = Status.LEGACY_USB_ENCRYPTED
                else:
                    raise ExportException(Status.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED)

        except ExportException:
            raise


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
                if self.cli.is_luks_volume(device):
                    volume = self.cli.get_luks_volume(device)
                    if not volume.writable:
                        unlocked = self.cli.unlock_luks_volume(
                            volume, self.submission.archive_metadata.encryption_key
                        )
                        mounted = self.cli.mount_volume(unlocked)

                    logger.debug(f"Export submission to {mounted.mountpoint}")
                    self.cli.write_data_to_device(self.submission.tmpdir, self.submission.target_dirname, mounted)

                else:
                    # Another kind of drive: VeraCrypt/TC, or unsupported
                    logger.error(f"Export failed because {device} is not supported")
                    raise ExportException(Status.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED)

        except ExportException as ex:
            raise

