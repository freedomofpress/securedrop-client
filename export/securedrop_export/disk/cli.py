import json
import logging
import os
import subprocess

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

        vol = Volume(device_name, EncryptionScheme.UNKNOWN)

        if device_fstype == "crypto_LUKS":
            logger.debug(f"{device_name} is LUKS-encrypted")
            vol.encryption = EncryptionScheme.LUKS

        children = device.get("children")
        if children:
            # It's an unlocked drive, possibly mounted
            if len(children) != 1:
                logger.error(f"Unexpected volume format on {device_name}")
                return None
            elif children[0].get("type") != "crypt":
                return None
            else:
                # Unlocked VC/TC drives will still have EncryptionScheme.UNKNOWN;
                # see if we can do better
                if vol.encryption == EncryptionScheme.UNKNOWN:
                    vol.encryption = self._is_it_veracrypt(vol)

                if children[0].get("mountpoint"):
                    logger.debug(f"{_DEV_PREFIX}{device_name} is mounted")
                    return MountedVolume(
                        device_name=device_name,
                        mapped_name=children[0].get("name"),
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
                        return self._mount_volume(vol, children[0].get("name"))

        # Locked VeraCrypt drives are rejected here (EncryptionScheme.UNKNOWN)
        if vol.encryption in (EncryptionScheme.LUKS, EncryptionScheme.VERACRYPT):
            logger.debug(f"{_DEV_PREFIX}{device_name} is supported export target")
            return vol
        else:
            logger.debug(f"No suitable volume found on {device_name}")
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
                    f"{_DEV_PREFIX}{volume.device_name}",
                ]
            ).decode("utf-8")
            if "IdType:                     crypto_TCRYPT\n" in info:
                return EncryptionScheme.VERACRYPT
            elif "IdType:                     crypto_LUKS\n" in info:
                # Don't downgrade LUKS to UNKNOWN if someone
                # calls this on a LUKS drive by accident
                return EncryptionScheme.LUKS
            else:
                return EncryptionScheme.UNKNOWN
        except subprocess.CalledProcessError as err:
            logger.debug(
                f"Error checking disk info of {_DEV_PREFIX}{volume.device_name}"
            )
            logger.error(err)
            # Not a showstopper
            return EncryptionScheme.UNKNOWN

    def unlock_volume(self, volume: Volume, encryption_key: str) -> MountedVolume:
        """
        Unlock and mount an encrypted volume. If volume is already mounted, preserve
        existing mountpoint.

        Throws ExportException if errors are encountered during device unlocking.
        """
        try:
            logger.debug("Unlocking volume {}".format(volume.device_name))
            p = subprocess.Popen(
                [
                    "udisksctl",
                    "unlock",
                    "--block-device",
                    volume.device_name,
                ],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            logger.debug("Passing key")
            _, err = p.communicate(input=str.encode(encryption_key, "utf-8"))
            rc = p.returncode

            # Unlocked
            if rc == 0 or (
                err is not None and "is already unlocked as" in err.decode("utf-8")
            ):
                logger.info("Device unlocked")

                mapped_name = self._get_mapped_name(volume)
                if mapped_name:
                    return self._mount_volume(volume, mapped_name)
                else:
                    # This is really covering our bases, we shouldn't get here
                    # if we already unlocked successfully.
                    logger.error(
                        f"No mapped device for {_DEV_PREFIX}{volume.device_name} found"
                    )
                    raise ExportException(sdstatus=Status.ERROR_UNLOCK_GENERIC)

            else:
                logger.error("Bad volume passphrase")
                raise ExportException(sdstatus=Status.ERROR_UNLOCK_LUKS)

        except subprocess.CalledProcessError as ex:
            logger.error(
                f"Error encountered while unlocking {_DEV_PREFIX}{volume.device_name}"
            )
            raise ExportException(sdstatus=Status.ERROR_UNLOCK_LUKS) from ex

    def _get_mapped_name(self, volume: Volume) -> Optional[str]:
        """
        Get name of mapped volume from a target device.
        Returns None if device is locked (no mapped name), throws ExportException on error.
        """
        try:
            items = (
                subprocess.check_output(
                    [
                        "lsblk",
                        f"{_DEV_PREFIX}{volume.device_name}",
                        "--raw",
                        "--noheadings",
                        "--output",
                        "NAME,TYPE",
                    ]
                )
                .decode("utf-8")
                .rstrip()
                .split("\n")
            )
            mapped_items = [
                i
                for i in items
                if i.endswith("crypt") and not i.startswith(f"{volume.device_name}")
            ]
            if len(mapped_items) == 1:
                # Space-separated name and type (eg `luks-123456-456789 crypt`)
                return mapped_items[0].split()[0]
            else:
                # Not an error, could just be a locked device or the wrong type of volume
                logger.info(
                    f"Found {len(mapped_items)} mapped volumes on {_DEV_PREFIX}{volume.device_name}"
                )

        except subprocess.CalledProcessError as e:
            logger.error("Error retrieving mapped volume name")
            raise ExportException(sdstatus=Status.DEVICE_ERROR) from e

    def _mount_volume(self, volume: Volume, mapped_name: str) -> MountedVolume:
        """
        Given an unlocked volume, mount volume in /media/user/ by udisksctl and
        return MountedVolume object.

        Raise ExportException if errors are encountered during mounting.
        """
        try:
            logger.info(f"Mount {_DEVMAPPER_PREFIX}{mapped_name} using udisksctl")
            subprocess.check_output(
                [
                    "udisksctl",
                    "mount",
                    "--block-device",
                    f"{_DEVMAPPER_PREFIX}{mapped_name}",
                ]
            )
        except subprocess.CalledProcessError as e:
            if (
                e.output is not None
                and "GDBus.Error:org.freedesktop.UDisks2.Error.AlreadyMounted"
                in e.output.decode("utf-8")
            ):
                logger.info("Already mounted")
            else:
                logger.error(e)
                raise ExportException(sdstatus=Status.ERROR_MOUNT) from e

        try:
            mountpoint = (
                subprocess.check_output(
                    [
                        "lsblk",
                        "--raw",
                        "--noheadings",
                        "--output",
                        "MOUNTPOINT",
                        f"{_DEVMAPPER_PREFIX}{mapped_name}",
                    ]
                )
                .decode("utf-8")
                .strip()
            )
            if mountpoint:
                return MountedVolume(
                    device_name=volume.device_name,
                    mapped_name=mapped_name,
                    encryption=volume.encryption,
                    mountpoint=mountpoint,
                )

            logger.error(
                f"Could not get mountpoint for {_DEV_PREFIX}{volume.device_name}"
            )
            raise ExportException(sdstatus=Status.ERROR_MOUNT)

        except subprocess.CalledProcessError as ex:
            logger.error(ex)
            raise ExportException(sdstatus=Status.ERROR_MOUNT) from ex

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
            raise ExportException(sdstatus=Status.ERROR_EXPORT) from ex

        finally:
            self.cleanup(device, submission_tmpdir)

    def cleanup(self, volume: MountedVolume, submission_tmpdir: str):
        """
        Post-export cleanup method. Unmount and lock drive and remove temporary
        directory. Currently called at end of `write_data_to_device()` to ensure
        device is always locked after export.

        Raise ExportException if errors during cleanup are encountered.
        """
        logger.debug("Syncing filesystems")
        try:
            subprocess.check_call(["sync"])
            self._close_volume(volume)
            self._remove_temp_directory(submission_tmpdir)

        except subprocess.CalledProcessError as ex:
            logger.error("Error syncing filesystem")
            raise ExportException(sdstatus=Status.ERROR_EXPORT_CLEANUP) from ex

    def _close_volume(self, mv: MountedVolume) -> Volume:
        """
        Unmount and close volume.
        """
        if os.path.exists(mv.mountpoint):
            logger.debug(f"Unmounting drive {mv.mapped_name} from {mv.mountpoint}")
            try:
                subprocess.check_call(
                    [
                        "udisksctl",
                        "unmount",
                        "--block-device",
                        f"{_DEVMAPPER_PREFIX}{mv.mapped_name}",
                    ]
                )

            except subprocess.CalledProcessError as ex:
                logger.error(ex)
                logger.error("Error unmounting device")

                # todo: return 'device busy' code
                raise ExportException(sdstatus=Status.ERROR_EXPORT_CLEANUP) from ex
        else:
            logger.info("Mountpoint does not exist; volume was already unmounted")

        if os.path.exists(f"{_DEVMAPPER_PREFIX}{mv.mapped_name}"):
            logger.debug(f"Closing drive {_DEV_PREFIX}{mv.device_name}")
            try:
                subprocess.check_call(
                    [
                        "udisksctl",
                        "lock",
                        "--block-device",
                        f"{_DEV_PREFIX}{mv.device_name}",
                    ]
                )

            except subprocess.CalledProcessError as ex:
                logger.error("Error closing device")
                raise ExportException(sdstatus=Status.ERROR_EXPORT_CLEANUP) from ex
        else:
            logger.info("Mapped entry does not exist; volume was already closed")

        return Volume(
            device_name=mv.device_name,
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
