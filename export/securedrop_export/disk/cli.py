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


class CLI:
    """
    A Python wrapper for shell commands required to detect, map, and
    mount USB devices.

    CLI callers must handle ExportException.
    """

    def get_volume(self) -> Volume:
        """
        Search for valid connected device.
        Raise ExportException on error.
        """
        logger.info("Checking connected volumes")
        try:
            # lsblk -o NAME,RM,RO,TYPE,MOUNTPOINT,FSTYPE --json
            lsblk = subprocess.check_output(
                ["lsblk", "--output", "NAME,RM,RO,TYPE,MOUNTPOINT,FSTYPE", "--json"]
            ).decode("utf-8")

            all_devices = json.loads(lsblk)

            if "blockdevices" not in all_devices:
                logger.error("No block devices found")
                raise ExportException(sdstatus=Status.NO_DEVICE_DETECTED)

            # Removable, non-read-only disks
            supported_devices = [
                item
                for item in all_devices.get("blockdevices")
                if item.get("type") == "disk"
                and item.get("rm") is True
                and item.get("ro") is False
            ]

            if len(supported_devices) == 0:
                raise ExportException(sdstatus=Status.NO_DEVICE_DETECTED)
            elif len(supported_devices) > 1:
                # For now we only support inserting one device at a time
                # during export. To support multi-device-select, parse
                # these results as well
                raise ExportException(sdstatus=Status.MULTI_DEVICE_DETECTED)
            else:
                return self._parse_single_device(supported_devices[0])

        except json.JSONDecodeError as err:
            logger.error(err)
            raise ExportException(sdstatus=Status.DEVICE_ERROR) from err

        except subprocess.CalledProcessError as ex:
            raise ExportException(sdstatus=Status.DEVICE_ERROR) from ex

    def _parse_single_device(self, block_device: dict) -> Union[Volume, MountedVolume]:
        """
        Given JSON-formatted lsblk output for one removable device, determine if it
        is suitably partitioned and return it to be used for export,
        mounting it if possible.

        A device may have nested output, with the partitions appearing
        as 'children.' It would be possible to parse and accept a highly nested
        partition scheme, but for simplicity, accept only disks that have an
        encrypted partition at either the whole-device level or the first partition
        level.

        Return MountedVolume (if writable) or Volume (if locked).

        Caller must handle ExportException.
        """
        volumes = []
        if "children" in block_device:
            for partition in block_device.get("children"):
                # /dev/sdX1, /dev/sdX2 etc
                item = self._get_supported_volume(partition)
                if item:
                    volumes.append(item)
        # /dev/sdX
        else:
            item = self._get_supported_volume(block_device)
            if item:
                volumes.append(item)

        # This restriction is only due to UI complexity--we don't offer users a
        # way to choose a specific target volume on their device.
        if len(volumes) != 1:
            logger.error(f"Need one target on {block_device}, got {len(volumes)}")
            raise ExportException(sdstatus=Status.INVALID_DEVICE_DETECTED)
            return volumes[0]

    def _get_supported_volume(
        self, device: dict
    ) -> Optional[Union[Volume, MountedVolume]]:
        """
        Helper. Return supported volume, mounting opportunistically if possible.

        Supported volumes:
          * Unlocked Veracrypt drives
          * Locked or unlocked LUKS drives
          * No more than one encrypted partition (multiple nonencrypted partitions
            are OK as they will be ignored).

        Note: It would be possible to support other unlocked encrypted drives, as long as
        udisks2 can tell they contain an encrypted partition.
        """
        device_name = device.get("name")
        device_fstype = device.get("fstype")

        vol = Volume(device_name, EncryptionScheme.UNKNOWN)

        if device_fstype == "crypto_LUKS":
            vol.encryption = EncryptionScheme.LUKS
        elif device_fstype == "crypto_TCRYPT":
            vol.encryption == EncryptionScheme.VERACRYPT

        # If drive is locked or is unsupported type, children will be None
        # (but in locked case, children will be shown once drive is unlocked)
        children = device.get("children")
        if children:
            # It's an unlocked drive, possibly mounted
            if len(children) != 1:
                logger.error(f"Unexpected volume format on {device_name}")
                return None
            # TODO: This is for supporting unknown encryption types if they are already mounted.
            # It's currently redundant due to check on line 147.
            elif children[0].get("type") != "crypt":
                logger.info("Not an encrypted partition")
                return None
            else:
                if children[0].get("mountpoint"):
                    logger.debug("Device is mounted")
                    return MountedVolume(
                        device_name=device_name,
                        mapped_name=children[0].get("name"),
                        encryption=vol.encryption,
                        mountpoint=children[0].get("mountpoint"),
                    )
                else:
                    # Try to mount it
                    return self._mount_volume(vol, children[0].get("name"))

        # We can decide whether or not to include locked vc drives here,
        # which would still have EncryptionScheme.UNKNOWN at this point,
        # but for now we aren't going to try to unlock them
        if vol.encryption in (EncryptionScheme.LUKS, EncryptionScheme.VERACRYPT):
            return vol
        else:
            logger.debug(f"No suitable volume found on {device_name}")
            return None

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
            p.communicate(input=str.encode(encryption_key, "utf-8")).decode("utf-8")
            rc = p.returncode

            # Unlocked, or was already unlocked
            if rc == 0 or rc == 1:
                logger.info("Device unlocked")

                mapped_name = self._get_mapped_name(volume)
                return self._mount_volume(volume, mapped_name)

            else:
                logger.error("Bad volume passphrase")
                # For now, we only try to unlock LUKS volumes.
                raise ExportException(sdstatus=Status.ERROR_UNLOCK_LUKS)

        except subprocess.CalledProcessError as ex:
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
                        f"{volume.device_name}",
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
                i for i in items if not i.startswith(f"{volume.device_name}")
            ]  # todo: if i.endswith("crypt") true for vc as well as luks?
            if len(mapped_items) == 1:
                # Space-separated name and type (eg `luks-123456-456789 crypt`)
                return mapped_items[0].split()[0]
            else:
                # Not an error, could just be a locked device or the wrong type of volume
                logger.info(
                    f"Found {len(mapped_items)} mapped volumes on {volume.device_name}"
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
            logger.info("Mount volume using udisksctl")
            exit_code, output = subprocess.getstatusoutput(
                [
                    "udisksctl",
                    "mount",
                    "--block-device",
                    f"{_DEVMAPPER_PREFIX}{mapped_name}",
                ]
            ).decode("utf-8")

            # Success (Mounted successfully, or was already mounted)
            if exit_code == 0 or exit_code == 1:
                mountpoint = (
                    subprocess.check_output(
                        [
                            "lsblk",
                            "--raw",
                            "--noheadings",
                            "--output",
                            "MOUNTPOINT",
                            f"{volume.device_name}",
                        ]
                    )
                    .decode("utf-8")
                    .strip()
                )
                return MountedVolume(
                    device_name=volume.device_name,
                    mapped_name=mapped_name,
                    mountpoint=mountpoint,
                )

            else:
                logger.error(
                    f"Could not mount {volume.device_name} (mount returned {exit_code})"
                )
                raise ExportException(sdstatus=Status.ERROR_MOUNT)

        except subprocess.CalledProcessError as ex:
            logger.error(ex)
            raise ExportException(sdstatus=Status.ERROR_MOUNT) from ex

    def write_data_to_device(
        self,
        submission_tmpdir: str,
        submission_target_dirname: str,
        device: MountedVolume,
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
            logger.debug(f"Unmounting drive from {mv.mountpoint}")
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
                logger.error("Error unmounting device")

                # todo: return 'device busy' code
                raise ExportException(sdstatus=Status.ERROR_EXPORT_CLEANUP) from ex
        else:
            logger.info("Mountpoint does not exist; volume was already unmounted")

        if os.path.exists(f"{_DEVMAPPER_PREFIX}{mv.mapped_name}"):
            logger.debug(f"Closing drive {mv.mapped_name}")
            try:
                subprocess.check_call(
                    [
                        "udisksctl",
                        "close",
                        "--block-device",
                        f"{_DEVMAPPER_PREFIX}{mv.mapped_name}",
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
