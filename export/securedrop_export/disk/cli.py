import json
import logging
import os
import pexpect
import re
import subprocess
import time

from typing import Optional, Union

from securedrop_export.exceptions import ExportException

from .volume import EncryptionScheme, Volume, MountedVolume
from .status import Status

logger = logging.getLogger(__name__)

_DEVMAPPER_PREFIX = "/dev/mapper/"
_DEV_PREFIX = "/dev/"
_UDISKS_PREFIX = (
    "MODEL                     REVISION  SERIAL               DEVICE\n"
    "--------------------------------------------------------------------------\n"
)


class CLI:
    """
    A Python wrapper for shell commands required to detect, map, and
    mount USB devices.

    CLI callers must handle ExportException.
    """

    def get_volume(self) -> Union[Volume, MountedVolume]:
        """
        Search for valid connected device.
        Raise ExportException on error.
        """
        logger.info("Checking connected volumes")
        try:
            usbs = (
                subprocess.check_output(["udisksctl", "status"])
                .decode("utf-8")
                .removeprefix(_UDISKS_PREFIX)
                .strip()
                .split("\n")
            )

            # Collect a space-separated list of USB device names.
            # Format:
            # Label (may contain spaces)    Revision   Serial#  Device
            # The last string is the device identifier (/dev/{device}).
            targets = []
            for i in usbs:
                item = i.strip().split()
                if len(item) > 0:
                    targets.append(item[-1])

            if len(targets) == 0:
                logger.info("No USB devices found")
                raise ExportException(sdstatus=Status.NO_DEVICE_DETECTED)
            elif len(targets) > 1:
                logger.error(
                    "Too many possibilities! Detach a storage device before continuing."
                )
                raise ExportException(sdstatus=Status.MULTI_DEVICE_DETECTED)

            # lsblk -o NAME,RM,RO,TYPE,MOUNTPOINT,FSTYPE --json
            # devices such as /dev/xvda are marked as "removable",
            # which is why we do the previous check to pick a device
            # recognized by udisks2
            lsblk = subprocess.check_output(
                [
                    "lsblk",
                    "--output",
                    "NAME,RO,TYPE,MOUNTPOINT,FSTYPE",
                    "--json",
                ]
            ).decode("utf-8")

            lsblk_json = json.loads(lsblk)
            if not lsblk_json.get("blockdevices"):
                logger.error("Unrecoverable: could not parse lsblk.")
                raise ExportException(sdstatus=Status.DEVICE_ERROR)

            volumes = []
            for device in lsblk_json.get("blockdevices"):
                if device.get("name") in targets and device.get("ro") is False:
                    logger.debug(
                        f"Checking removable, writable device {_DEV_PREFIX}{device.get('name')}"
                    )
                    # Inspect partitions or whole volume.
                    # For sanity, we will only support encrypted partitions one level deep.
                    if "children" in device:
                        for partition in device.get("children"):
                            # /dev/sdX1, /dev/sdX2 etc
                            item = self._get_supported_volume(partition)
                            if item:
                                volumes.append(item)
                    # /dev/sdX
                    else:
                        item = self._get_supported_volume(device)
                        if item:
                            volumes.append(item)

            if len(volumes) != 1:
                logger.error(f"Need one target, got {len(volumes)}")
                raise ExportException(sdstatus=Status.INVALID_DEVICE_DETECTED)
            else:
                logger.debug(f"Export target is {volumes[0].device_name}")
                return volumes[0]

        except json.JSONDecodeError as err:
            logger.error(err)
            raise ExportException(sdstatus=Status.DEVICE_ERROR) from err

        except subprocess.CalledProcessError as ex:
            raise ExportException(sdstatus=Status.DEVICE_ERROR) from ex

    def _get_supported_volume(
        self, device: dict
    ) -> Optional[Union[Volume, MountedVolume]]:
        """
        Given JSON-formatted lsblk output for one device, determine if it
        is suitably partitioned and return it to be used for export,
        mounting it if possible.

        Supported volumes:
          * Unlocked Veracrypt drives
          * Locked or unlocked LUKS drives
          * No more than one encrypted partition (multiple non-encrypted partitions
            are OK as they will be ignored).

        Note: It would be possible to support other unlocked encrypted drives, as long as
        udisks2 can tell they contain an encrypted partition.
        """
        device_name = device.get("name")
        device_fstype = device.get("fstype")

        vol = Volume(f"{_DEV_PREFIX}{device_name}", EncryptionScheme.UNKNOWN)

        if device_fstype == "crypto_LUKS":
            logger.debug(f"{device_name} is LUKS-encrypted")
            vol.encryption = EncryptionScheme.LUKS

        children = device.get("children")
        if children:
            if len(children) != 1:
                logger.error(f"Unexpected volume format on {vol.device_name}")
                return None
            elif children[0].get("type") != "crypt":
                return None
            else:
                # It's an unlocked drive, possibly mounted
                mapped_name = f"{_DEVMAPPER_PREFIX}{children[0].get('name')}"

                # Unlocked VC/TC drives will still have EncryptionScheme.UNKNOWN;
                # see if we can do better
                if vol.encryption == EncryptionScheme.UNKNOWN:
                    vol.encryption = self._is_it_veracrypt(vol)

                if children[0].get("mountpoint"):
                    logger.debug(f"{vol.device_name} is mounted")

                    return MountedVolume(
                        device_name=vol.device_name,
                        unlocked_name=mapped_name,
                        encryption=vol.encryption,
                        mountpoint=children[0].get("mountpoint"),
                    )
                else:
                    # To opportunistically mount any unlocked encrypted partition
                    # (i.e. third-party devices such as IronKeys), remove this condition.
                    if vol.encryption in (
                        EncryptionScheme.LUKS,
                        EncryptionScheme.VERACRYPT,
                    ):
                        logger.debug(
                            f"{device_name} is unlocked but unmounted; attempting mount"
                        )
                        return self._mount_volume(vol, mapped_name)

        # Locked VeraCrypt drives are rejected here (EncryptionScheme.UNKNOWN)
        if vol.encryption in (EncryptionScheme.LUKS, EncryptionScheme.VERACRYPT):
            logger.debug(f"{vol.device_name} is supported export target")
            return vol
        else:
            logger.debug(f"No suitable volume found on {vol.device_name}")
            return None

    def _is_it_veracrypt(self, volume: Volume) -> EncryptionScheme:
        """
        Helper. Best-effort detection of unlocked VeraCrypt drives.
        Udisks2 requires the flag file /etc/udisks2/tcrypt.conf to
        enable VC detection, which we will ship with the `securedrop-export` package.
        """
        try:
            info = subprocess.check_output(
                [
                    "udisksctl",
                    "info",
                    "--block-device",
                    f"{volume.device_name}",
                ]
            ).decode("utf-8")
            if "IdType:                     crypto_TCRYPT\n" in info:
                return EncryptionScheme.VERACRYPT
            elif "IdType:                     crypto_LUKS\n" in info:
                # Don't downgrade LUKS to UNKNOWN if someone
                # calls this method on a LUKS drive
                return EncryptionScheme.LUKS
            else:
                return EncryptionScheme.UNKNOWN
        except subprocess.CalledProcessError as err:
            logger.debug(f"Error checking disk info of {volume.device_name}")
            logger.error(err)
            # Not a showstopper
            return EncryptionScheme.UNKNOWN

    def unlock_volume(self, volume: Volume, encryption_key: str) -> MountedVolume:
        """
        Unlock and mount an encrypted volume. If volume is already mounted, preserve
        existing mountpoint.

        Throws ExportException if errors are encountered during device unlocking.

        `pexpect.ExeptionPexpect` can't be try/caught, since it's not a
        child of BaseException, but instead, exceptions can be included
        in the list of results to check for. (See
        https://pexpect.readthedocs.io/en/stable/api/pexpect.html#pexpect.spawn.expect)
        """
        logger.debug("Unlocking volume {}".format(volume.device_name))

        command = f"udisksctl unlock --block-device {volume.device_name}"
        prompt = ["Passphrase: ", pexpect.EOF, pexpect.TIMEOUT]
        expected = [
            f"Unlocked {volume.device_name} as (.*)\.",
            "GDBus.Error:org.freedesktop.UDisks2.Error.Failed: Device "  # string continues
            f"{volume.device_name} is already unlocked as (.*)\.",
            "GDBus.Error:org.freedesktop.UDisks2.Error.Failed: Error "  # string continues
            f"unlocking {volume.device_name}: Failed to activate device: Incorrect passphrase",
            pexpect.EOF,
            pexpect.TIMEOUT,
        ]
        unlock_error = Status.ERROR_UNLOCK_GENERIC

        child = pexpect.spawn(command)
        index = child.expect(prompt)
        if index != 0:
            logger.error("Did not receive disk unlock prompt")
            raise ExportException(sdstatus=Status.ERROR_UNLOCK_GENERIC)
        else:
            logger.debug("Passing key")
            child.sendline(encryption_key)
            index = child.expect(expected)
            if index == 0 or index == 1:
                # We know what format the string is in
                dm_name = child.match.group(1).decode("utf-8").strip()
                logger.debug(f"Device is unlocked as {dm_name}")

                child.close()
                if (child.exitstatus) not in (0, 1):
                    logger.warning(f"pexpect: child exited with {child.exitstatus}")

                # dm_name format is /dev/dm-X
                return self._mount_volume(volume, dm_name)

            elif index == 2:
                # Still an error, but we can report more specific error to the user
                logger.debug("Bad volume passphrase")
                unlock_error = Status.ERROR_UNLOCK_LUKS

            # Any other index values are also an error. Clean up and raise
            child.close()

            logger.error(f"Error encountered while unlocking {volume.device_name}")
            raise ExportException(sdstatus=unlock_error)

    def _mount_volume(self, volume: Volume, full_unlocked_name: str) -> MountedVolume:
        """
        Given an unlocked volume, mount volume in /media/user/ by udisksctl and
        return MountedVolume object.

        Unlocked name could be `/dev/mapper/$id` or `/dev/dm-X`.

        Raise ExportException if errors are encountered during mounting.

        `pexpect.ExeptionPexpect` can't be try/caught, since it's not a
        child of BaseException, but instead, exceptions can be included
        in the list of results to check for. (See
        https://pexpect.readthedocs.io/en/stable/api/pexpect.html#pexpect.spawn.expect)
        """

        info = f"udisksctl info --block-device {volume.device_name}"
        # \x1b[37mPreferredDevice:\x1b[0m            /dev/sdaX\r\n
        expected_info = [
            f"*PreferredDevice:[\t+]{volume.device_name}\r\n",
            "*Error looking up object for device*",
            pexpect.EOF,
            pexpect.TIMEOUT,
        ]
        max_retries = 3

        unlock = f"udisksctl mount --block-device {full_unlocked_name}"

        # We can't pass {full_unlocked_name} in the match statement since even if we
        # pass in /dev/mapper/xxx, udisks2 may refer to the disk as /dev/dm-X.
        expected_unlock = [
            f"Mounted * at (.*)",
            f"Error mounting *: GDBus.Error:org."  # string continues
            "freedesktop.UDisks2.Error.AlreadyMounted: "  # string continues
            "Device .* is already mounted at `(.*)'",
            f"Error looking up object for device *.",
            pexpect.EOF,
            pexpect.TIMEOUT,
        ]
        mountpoint = None

        logger.debug(f"Check to make sure udisks identified {volume.device_name} "
                     "(unlocked as {full_unlocked_name})")
        for _ in range(max_retries):
            child = pexpect.spawn(info)
            index = child.expect(expected_info)
            logger.debug(f"Results from udisks info: {volume.device_name}, "
                         "before: {child.before}, after: {child.after}")
            child.close()

            if index != 0:
                logger.debug(f"index {index}")
                logger.warning(
                    f"udisks can't identify {volume.device_name}, retrying..."
                )
                time.sleep(0.5)
            else:
                print(f"udisks found {volume.device_name}")
                break

        logger.info(f"Mount {full_unlocked_name} using udisksctl")
        child = pexpect.spawn(unlock)
        index = child.expect(expected_unlock)

        logger.debug(
            f"child: {str(child.match)}, before: {child.before}, after: {child.after}"
        )

        if index == 0:
            # As above, we know the format
            mountpoint = child.match.group(1).decode("utf-8").strip()
            logger.debug(f"Successfully mounted device at {mountpoint}")

        elif index == 1:
            # Mountpoint needs a bit of help. It arrives in the form `/path/to/mountpoint'.
            # including the one backtick, single quote, and the period
            mountpoint = child.match.group(1).decode("utf-8").strip()
            logger.debug(f"Device already mounted at {mountpoint}")

        elif index == 2:
            logger.debug("Device is not ready")

        child.close()

        if mountpoint:
            return MountedVolume(
                device_name=volume.device_name,
                unlocked_name=full_unlocked_name,
                encryption=volume.encryption,
                mountpoint=mountpoint,
            )

        logger.error("Could not get mountpoint")
        raise ExportException(sdstatus=Status.ERROR_MOUNT)

    def write_data_to_device(
        self,
        device: MountedVolume,
        submission_tmpdir: str,
        submission_target_dirname: str,
    ):
        """
        Move files to drive (overwrites files with same filename) and unmount drive.

        Drive is unmounted and files are cleaned up as part of the `finally` block to ensure
        that cleanup happens even if export fails or only partially succeeds.
        """

        try:
            # Flag to pass to cleanup method
            is_error = False

            target_path = os.path.join(device.mountpoint, submission_target_dirname)
            subprocess.check_call(["mkdir", target_path])

            export_data = os.path.join(submission_tmpdir, "export_data/")
            logger.debug("Copying file to {}".format(submission_target_dirname))

            subprocess.check_call(["cp", "-r", export_data, target_path])
            logger.info(
                "File copied successfully to {}".format(submission_target_dirname)
            )

        except (subprocess.CalledProcessError, OSError) as ex:
            logger.error(ex)

            # Ensure we report an export error out after cleanup
            is_error = True
            raise ExportException(sdstatus=Status.ERROR_EXPORT) from ex

        finally:
            self.cleanup(device, submission_tmpdir, is_error)

    def cleanup(
        self,
        volume: MountedVolume,
        submission_tmpdir: str,
        is_error: bool = False,
        should_close_volume: bool = True,
    ):
        """
        Post-export cleanup method. Unmount and lock drive and remove temporary
        directory.

        Raises ExportException if errors during cleanup are encountered.

        Method is called whether or not export succeeds; if `is_error` is True,
        will report export error status on error (insted of cleanup status).
        """
        error_status = Status.ERROR_EXPORT if is_error else Status.ERROR_EXPORT_CLEANUP

        logger.debug("Syncing filesystems")
        try:
            subprocess.check_call(["sync"])
            self._remove_temp_directory(submission_tmpdir)

            # Future configurable option
            if should_close_volume:
                self._close_volume(volume)

        except subprocess.CalledProcessError as ex:
            logger.error("Error syncing filesystem")
            raise ExportException(sdstatus=error_status) from ex

    def _close_volume(self, mv: MountedVolume) -> Volume:
        """
        Unmount and close volume.
        """
        if os.path.exists(mv.mountpoint):
            logger.debug(f"Unmounting drive {mv.unlocked_name} from {mv.mountpoint}")
            try:
                subprocess.check_call(
                    [
                        "udisksctl",
                        "unmount",
                        "--block-device",
                        f"{mv.unlocked_name}",
                    ]
                )

            except subprocess.CalledProcessError as ex:
                logger.error(ex)
                logger.error("Error unmounting device")

                raise ExportException(sdstatus=Status.ERROR_UNMOUNT_VOLUME_BUSY) from ex
        else:
            logger.info("Mountpoint does not exist; volume was already unmounted")

        if os.path.exists(f"{mv.unlocked_name}"):
            logger.debug(f"Closing drive {mv.device_name}")
            try:
                subprocess.check_call(
                    [
                        "udisksctl",
                        "lock",
                        "--block-device",
                        f"{mv.device_name}",
                    ]
                )

            except subprocess.CalledProcessError as ex:
                logger.error("Error closing device")
                raise ExportException(sdstatus=Status.ERROR_EXPORT_CLEANUP) from ex
        else:
            logger.info("Mapped entry does not exist; volume was already closed")

        return Volume(
            device_name=f"{_DEV_PREFIX}{mv.device_name}",
            encryption=mv.encryption,
        )

    def _remove_temp_directory(self, tmpdir: str):
        """
        Helper. Remove temporary directory used during export.
        """
        logger.debug(f"Deleting temporary directory {tmpdir}")
        try:
            subprocess.check_call(["rm", "-rf", tmpdir])
        except subprocess.CalledProcessError as ex:
            logger.error("Error removing temporary directory")
            raise ExportException(sdstatus=Status.ERROR_EXPORT_CLEANUP) from ex
