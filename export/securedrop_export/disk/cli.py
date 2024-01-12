import json
import logging
import os
import subprocess

from typing import List, Optional, Union

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
        See if we have a valid connected device.

        Raise ExportException if any commands fail.
        """
        logger.info("Checking connected volumes")
        try:
            # lsblk -o NAME,RM,RO,TYPE,MOUNTPOINT,FSTYPE --json
            lsblk = subprocess.check_output(
                ["lsblk", "--output", "NAME,RM,RO,TYPE,MOUNTPOINT,FSTYPE", "--json"]
            ).decode("utf-8")
            all_devices = json.loads(lsblk)

            # Removable, non-read-only disks
            removable_devices = [
                item
                for item in all_devices.get("blockdevices")
                if item.get("type") == "disk"
                and item.get("rm") is True
                and item.get("ro") is False
            ]

            if len(removable_devices) == 0:
                raise ExportException(sdstatus=Status.NO_DEVICE_DETECTED)
            elif len(removable_devices) > 1:
                # For now we only support inserting one device at a time
                # during export. To support multi-device-select we would parse
                # these results as well
                raise ExportException(sdstatus=Status.MULTI_DEVICE_DETECTED)
            else:
                return self._parse_single_device(removable_devices[0])
        
        except ExportException:
            raise

        except subprocess.CalledProcessError as ex:
            raise ExportException(sdstatus=Status.DEVICE_ERROR) from ex


    def _parse_single_device(self, block_device: dict) -> Volume:
        """
        Given a JSON-formatted lsblk output for one device, determine if it
        is suitably partitioned and return Volume to be used for export.
 
        A device may have nested output, with the partitions appearing
        as 'children.' It would be possible to parse and accept a highly nested
        partition scheme, but for simplicity, accept only disks that have an
        encrypted partition at either the whole-device level or the first partition
        level.

           Acceptable disks:
          * Unlocked Veracrypt drives
          * Locked or unlocked LUKS drives
          * No more than one encrypted partition (multiple nonencrypted partitions
            are OK as they will be ignored).

        Returns Volume or throws ExportException.  
        """
        volumes = []
        if "children" in block_device:
            for entry in block_device.get("children"):
                if "children" in entry:
                    # /dev/sdX1, /dev/sdX2 etc
                    for partition in entry.get("children"):
                        volumes.append(self._get_supported_volume(entry, partition))
                # /dev/sdX
                else:
                    volumes.append(self._get_supported_volume(block_device, entry))

        # This restriction is only due to UI complexity--we don't offer users a
        # way to choose a specific target volume on their device.
        if len(volumes) != 1:
            logger.error(f"Need one target on {block_device}, got {len(volumes)}")
            raise ExportException(sdstatus=Status.INVALID_DEVICE_DETECTED)
            return volumes[0]
 
    def _get_supported_volume(
        self, device, partition
    ) -> Optional[Union[Volume, MountedVolume]]:
        """
        Return supported volume.
        Will only return devices that are confirmed supported (meaning, LUKS drives
        or unlocked Veracrypt drives. Locked Veracrypt drives are excluded).
        """
        device_name = device.get("name")
        mapped_name = partition.get("name")
        mountpoint = partition.get("mountpoint")

        # If the device has a mountpoint then it can be fully checked out to see if it's supported.
        # If not then (for now) its parent has to have file system type `crypto_LUKS` to be supported.
        if mountpoint is not None:
            encryption = self._get_cryptsetup_info(mapped_name)
            if encryption in (EncryptionScheme.LUKS, EncryptionScheme.VERACRYPT):
                return MountedVolume(
                    device_name=device_name,
                    mapped_name=mapped_name,
                    encryption=encryption,
                    mountpoint=mountpoint,
                )
            else:
                logger.info(f"Unsupported device {device_name}")
        elif device.get("fstype") == "crypto_LUKS":
            return Volume(
                device_name=device_name,
                encryption=EncryptionScheme.LUKS,
            )
        else:
            logger.info("No suitable volumes found")
 
    def _get_cryptsetup_info(self, entry) -> EncryptionScheme:
        """
        Given a volume, return information about its encryption scheme,
        if applicable.
        """
        status = (
            subprocess.check_output(
                ["sudo", "cryptsetup", "status", f"{_DEVMAPPER_PREFIX}{entry}"]
             )
            .decode("utf-8")
            .split("\n  ")
        )
 
        if "type:    TCRYPT" in status:
            return EncryptionScheme.VERACRYPT
        elif "type:    LUKS1" in status or "type:    LUKS2" in status:
            return EncryptionScheme.LUKS
        else:
            return EncryptionScheme.UNKNOWN

    def unlock_volume(self, volume: Volume, encryption_key: str) -> MountedVolume:
        """
        Unlock and mount an encrypted volume. If volume is already mounted, preserve
        existing mountpoint.

        Raise ExportException if errors are encountered during device unlocking.
        """
        if isinstance(volume, MountedVolume):
            logger.info("Volume is already mounted")
            return volume
        else:
            try:
                logger.debug("Unlocking volume {}".format(volume.device_name))

                # an alternative is udisksctl unlock -b /dev/sdX (and then password prompt) for luks, not usure about vc.
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
                result = p.communicate(input=str.encode(encryption_key, "utf-8")).decode("utf-8")
                rc = p.returncode

                if rc == 0:
                    # todo check result for location of mapped drive
                    logger.info(f"result: {result}")
                    # Success is "Mounted $device at $path"
                    if result.startswith("Unlocked "):
                        mapped_name = result.split()[-1]

                        return self.mount_volume(volume, mapped_name)

                    logger.debug("Successfully unlocked.")
                else:
                    logger.error("Bad volume passphrase")
                    # For now, we only try to unlock LUKS volumes.
                    raise ExportException(sdstatus=Status.ERROR_UNLOCK_LUKS)

            except subprocess.CalledProcessError as ex:
                raise ExportException(sdstatus=Status.DEVICE_ERROR) from ex
            
    # # Not currently in use
    # def attempt_unlock_veracrypt(
    #     self, volume: Volume, encryption_key: str
    # ) -> MountedVolume:
    #     """
    #     Attempt to unlock and mount a presumed-Veracrypt drive at the default mountpoint.
    #     """
    #     try:
    #         p = subprocess.Popen(
    #             [
    #                 "sudo",
    #                 "cryptsetup",
    #                 "open",
    #                 "--type",
    #                 "tcrypt",
    #                 "--veracrypt",
    #                 f"{volume.device_name}",
    #                 f"{_DEFAULT_EXPORT_NAME}",
    #             ],
    #             stdout=subprocess.PIPE,
    #             stderr=subprocess.PIPE,
    #         )
    #         p.communicate(input=str.encode(encryption_key, "utf-8"))
    #         rc = p.returncode

    #         if rc == 0:
    #             volume.encryption = EncryptionScheme.VERACRYPT

    #             # Mapped name is /dev/mapper/${_DEFAULT_EXPORT_NAME}
    #             return self.mount_volume(volume, _DEFAULT_EXPORT_NAME)

    #         else:
    #             # Something was wrong and we could not unlock.
    #             logger.error("Unlocking failed. Bad passphrase, or unsuitable volume.")
    #             raise ExportException(sdstatus=Status.ERROR_UNLOCK_GENERIC)

    #     except subprocess.CalledProcessError as error:
    #         logger.error("Error during unlock/mount attempt.")
    #         logger.debug(error)
    #         raise ExportException(sdstatus=Status.ERROR_UNLOCK_GENERIC)

    def _mount_volume(self, volume: Volume, mapped_name: str) -> MountedVolume:
        """
        Given an unlocked volume, mount volume in /media/user/ by udisksctl and
        return MountedVolume object.

        Raise ExportException if errors are encountered during mounting.
        """
        try:
            logger.info("Mount volume in /media/user using udisksctl")
            output = subprocess.check_output(
                ["udisksctl", "mount", "--block-device", f"{_DEVMAPPER_PREFIX}{mapped_name}"]
            ).decode("utf-8")

            # Success is "Mounted $device at $path"
            if output.startswith("Mounted "):
                mountpoint = output.split()[-1]
            else:
                # it didn't successfully mount, but also exited with code 0?
                raise ExportException(sdstatus=Status.ERROR_MOUNT)

            return MountedVolume.from_volume(volume, mapped_name=mapped_name, mountpoint=mountpoint)

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
            self.cleanup_drive_and_tmpdir(device, submission_tmpdir)

    def cleanup_drive_and_tmpdir(self, volume: MountedVolume, submission_tmpdir: str):
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
                subprocess.check_call(["udisksctl", "unmount", "--block-device", f"{_DEVMAPPER_PREFIX}{mv.mapped_name}"])

            except subprocess.CalledProcessError as ex:
                logger.error("Error unmounting device")
                raise ExportException(sdstatus=Status.ERROR_EXPORT_CLEANUP) from ex
        else:
            logger.info("Mountpoint does not exist; volume was already unmounted")

        if os.path.exists(f"{_DEVMAPPER_PREFIX}{mv.mapped_name}"):
            logger.debug(f"Closing drive")
            try:
                subprocess.check_call(
                    ["udisksctl", "close", "--block-device", f"{_DEVMAPPER_PREFIX}{mv.mapped_name}"]
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
        Helper. Remove temporary directory used during archive export.
        """
        logger.debug(f"Deleting temporary directory {tmpdir}")
        try:
            subprocess.check_call(["rm", "-rf", tmpdir])
        except subprocess.CalledProcessError as ex:
            logger.error("Error removing temporary directory")
            raise ExportException(sdstatus=Status.ERROR_EXPORT_CLEANUP) from ex
