import logging
import os
import subprocess
import sys

from typing import List

from securedrop_export.export import ExportAction
from securedrop_export.exceptions import ExportStatus

MOUNTPOINT = "/media/usb"
ENCRYPTED_DEVICE = "encrypted_volume"

logger = logging.getLogger(__name__)


class DiskAction(ExportAction):
    def __init__(self, submission):
        self.submission = submission
        self.device = None  # Optional[str]
        self.mountpoint = MOUNTPOINT
        self.encrypted_device = ENCRYPTED_DEVICE

    def run(self) -> None:
        """Run logic"""
        raise NotImplementedError

    def check_usb_connected(self, exit=False) -> None:
        usb_devices = self._get_connected_usbs()

        if len(usb_devices) == 0:
            logger.info("0 USB devices connected")
            self.submission.exit_gracefully(ExportStatus.USB_NOT_CONNECTED.value)
        elif len(usb_devices) == 1:
            logger.info("1 USB device connected")
            self.device = usb_devices[0]
            if exit:
                self.submission.exit_gracefully(ExportStatus.USB_CONNECTED.value)
        elif len(usb_devices) > 1:
            logger.info(">1 USB devices connected")
            # Return generic error until freedomofpress/securedrop-export/issues/25
            self.submission.exit_gracefully(ExportStatus.ERROR_GENERIC.value)

    def _get_connected_usbs(self) -> List[str]:
        logger.info("Performing usb preflight")
        # List all block devices attached to VM that are disks and not partitions.
        try:
            lsblk = subprocess.Popen(
                ["lsblk", "-o", "NAME,TYPE"],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            grep = subprocess.Popen(
                ["grep", "disk"],
                stdin=lsblk.stdout,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            command_output = grep.stdout.readlines()

            # The first word in each element of the command_output list is the device name
            attached_devices = [x.decode("utf8").split()[0] for x in command_output]
        except subprocess.CalledProcessError:
            self.submission.exit_gracefully(ExportStatus.ERROR_GENERIC.value)

        # Determine which are USBs by selecting those block devices that are removable disks.
        usb_devices = []
        for device in attached_devices:
            try:
                removable = subprocess.check_output(
                    ["cat", "/sys/class/block/{}/removable".format(device)],
                    stderr=subprocess.PIPE,
                )
                is_removable = int(removable.decode("utf8").strip())
            except subprocess.CalledProcessError:
                is_removable = False

            if is_removable:
                usb_devices.append("/dev/{}".format(device))

        return usb_devices

    def set_extracted_device_name(self):
        try:
            device_and_partitions = subprocess.check_output(
                ["lsblk", "-o", "TYPE", "--noheadings", self.device],
                stderr=subprocess.PIPE,
            )

            # we don't support multiple partitions
            partition_count = (
                device_and_partitions.decode("utf-8").split("\n").count("part")
            )
            if partition_count > 1:
                logger.debug("multiple partitions not supported")
                self.submission.exit_gracefully(
                    ExportStatus.USB_ENCRYPTION_NOT_SUPPORTED.value
                )

            # redefine device to /dev/sda if disk is encrypted, /dev/sda1 if partition encrypted
            self.device = self.device if partition_count == 0 else self.device + "1"
        except subprocess.CalledProcessError:
            self.submission.exit_gracefully(
                ExportStatus.USB_ENCRYPTION_NOT_SUPPORTED.value
            )

    def check_luks_volume(self):
        # cryptsetup isLuks returns 0 if the device is a luks volume
        # subprocess with throw if the device is not luks (rc !=0)
        logger.info("Checking if volume is luks-encrypted")
        self.set_extracted_device_name()
        logger.debug("checking if {} is luks encrypted".format(self.device))
        self.submission.safe_check_call(
            command=["sudo", "cryptsetup", "isLuks", self.device],
            error_message=ExportStatus.USB_ENCRYPTION_NOT_SUPPORTED.value,
        )
        self.submission.exit_gracefully(ExportStatus.USB_ENCRYPTED.value)

    def unlock_luks_volume(self, encryption_key):
        try:
            # get the encrypted device name
            self.set_extracted_device_name()
            luks_header = subprocess.check_output(
                ["sudo", "cryptsetup", "luksDump", self.device]
            )
            luks_header_list = luks_header.decode("utf-8").split("\n")
            for line in luks_header_list:
                items = line.split("\t")
                if "UUID" in items[0]:
                    self.encrypted_device = "luks-" + items[1]

            # the luks device is already unlocked
            if os.path.exists(os.path.join("/dev/mapper/", self.encrypted_device)):
                logger.debug("Device already unlocked")
                return

            logger.debug("Unlocking luks volume {}".format(self.encrypted_device))
            p = subprocess.Popen(
                ["sudo", "cryptsetup", "luksOpen", self.device, self.encrypted_device],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            logger.debug("Passing key")
            p.communicate(input=str.encode(encryption_key, "utf-8"))
            rc = p.returncode
            if rc != 0:
                logger.error("Bad phassphrase for {}".format(self.encrypted_device))
                self.submission.exit_gracefully(ExportStatus.USB_BAD_PASSPHRASE.value)
        except subprocess.CalledProcessError:
            self.submission.exit_gracefully(ExportStatus.USB_ENCRYPTION_NOT_SUPPORTED)

    def mount_volume(self):
        # If the drive is already mounted then we don't need to mount it again
        output = subprocess.check_output(
            ["lsblk", "-o", "MOUNTPOINT", "--noheadings", self.device]
        )
        mountpoint = output.decode("utf-8").strip()
        if mountpoint:
            logger.debug("The device is already mounted")
            self.mountpoint = mountpoint
            return

        # mount target not created, create folder
        if not os.path.exists(self.mountpoint):
            self.submission.safe_check_call(
                command=["sudo", "mkdir", self.mountpoint],
                error_message=ExportStatus.ERROR_USB_MOUNT,
            )

        mapped_device_path = os.path.join("/dev/mapper/", self.encrypted_device)
        logger.info("Mounting {}".format(mapped_device_path))
        self.submission.safe_check_call(
            command=["sudo", "mount", mapped_device_path, self.mountpoint],
            error_message=ExportStatus.ERROR_USB_MOUNT.value,
        )
        self.submission.safe_check_call(
            command=["sudo", "chown", "-R", "user:user", self.mountpoint],
            error_message=ExportStatus.ERROR_USB_MOUNT.value,
        )

    def copy_submission(self):
        # move files to drive (overwrites files with same filename) and unmount drive
        # we don't use safe_check_call here because we must lock and
        # unmount the drive as part of the finally block
        try:
            target_path = os.path.join(self.mountpoint, self.submission.target_dirname)
            subprocess.check_call(["mkdir", target_path])
            export_data = os.path.join(self.submission.tmpdir, "export_data/")
            logger.info("Copying file to {}".format(self.submission.target_dirname))
            subprocess.check_call(["cp", "-r", export_data, target_path])
            logger.info(
                "File copied successfully to {}".format(self.submission.target_dirname)
            )
        except (subprocess.CalledProcessError, OSError):
            self.submission.exit_gracefully(ExportStatus.ERROR_USB_WRITE.value)
        finally:
            logger.info("Syncing filesystems")
            subprocess.check_call(["sync"])

            if os.path.exists(self.mountpoint):
                logger.info("Unmounting drive from {}".format(self.mountpoint))
                subprocess.check_call(["sudo", "umount", self.mountpoint])

            if os.path.exists(os.path.join("/dev/mapper", self.encrypted_device)):
                logger.info("Locking luks volume {}".format(self.encrypted_device))
                subprocess.check_call(
                    ["sudo", "cryptsetup", "luksClose", self.encrypted_device]
                )

            logger.info(
                "Deleting temporary directory {}".format(self.submission.tmpdir)
            )
            subprocess.check_call(["rm", "-rf", self.submission.tmpdir])
            sys.exit(0)


class USBTestAction(DiskAction):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def run(self):
        logger.info("Export archive is usb-test")
        self.check_usb_connected(exit=True)


class DiskTestAction(DiskAction):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def run(self):
        logger.info("Export archive is disk-test")
        # check_usb_connected looks for the drive, sets the drive to use
        self.check_usb_connected()
        self.check_luks_volume()


class DiskExportAction(DiskAction):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def run(self):
        logger.info("Export archive is disk")
        # check_usb_connected looks for the drive, sets the drive to use
        self.check_usb_connected()
        logger.info("Unlocking volume")
        # exports all documents in the archive to luks-encrypted volume
        self.unlock_luks_volume(self.submission.archive_metadata.encryption_key)
        logger.info("Mounting volume")
        self.mount_volume()
        logger.info("Copying submission to drive")
        self.copy_submission()
