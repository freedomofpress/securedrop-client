import logging

from securedrop_export.archive import Archive
from securedrop_export.exceptions import ExportException

from .cli import CLI
from .status import Status
from .volume import MountedVolume, Volume

logger = logging.getLogger(__name__)


class Service:
    """
    Actions that can be performed against USB device(s).
    This is the "API" portion of the export workflow.
    """

    def __init__(self, submission: Archive, cli: CLI = CLI()):
        self.cli = cli
        self.submission = submission

    def scan_all_devices(self) -> Status:
        """
        Check all connected devices and return current device
        status.
        """
        try:
            volume = self.cli.get_volume()
            if isinstance(volume, MountedVolume):
                return Status.DEVICE_WRITABLE
            elif isinstance(volume, Volume):
                return Status.DEVICE_LOCKED
            else:
                # Above will return MountedVolume, Volume, or raise error;
                # this shouldn't be reachable
                raise ExportException(sdstatus=Status.DEVICE_ERROR)

        except ExportException as ex:
            logger.debug(ex)
            status = ex.sdstatus if ex.sdstatus is not None else Status.DEVICE_ERROR
            logger.error(f"Encountered {status.value} while checking volumes")
            return status

    def export(self) -> Status:
        """
        Export material to USB drive.
        """
        try:
            volume = self.cli.get_volume()
            if isinstance(volume, MountedVolume):
                logger.debug("Mounted volume detected, exporting files")
                self.cli.write_data_to_device(
                    volume, self.submission.tmpdir, self.submission.target_dirname
                )
                return Status.SUCCESS_EXPORT
            elif isinstance(volume, Volume):
                if self.submission.encryption_key is not None:
                    logger.debug("Volume is locked, try unlocking")
                    mv = self.cli.unlock_volume(volume, self.submission.encryption_key)
                    if isinstance(mv, MountedVolume):
                        logger.debug("Export to device")
                        # Exports then locks the drive.
                        # If the export succeeds but the drive is in use, will raise
                        # exception.
                        self.cli.write_data_to_device(
                            mv, self.submission.tmpdir, self.submission.target_dirname
                        )
                        return Status.SUCCESS_EXPORT
                    else:
                        raise ExportException(sdstatus=Status.ERROR_UNLOCK_GENERIC)
                else:
                    logger.info("Volume is locked and no key has been provided")
                    return Status.DEVICE_LOCKED

        except ExportException as ex:
            logger.debug(ex)
            status = ex.sdstatus if ex.sdstatus is not None else Status.ERROR_EXPORT
            logger.error(f"Enountered {status.value} while trying to export")
            return status
