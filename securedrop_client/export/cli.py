import logging
import subprocess
from enum import Enum
from shlex import quote
from typing import List, Optional

from .archive import Archive

logger = logging.getLogger(__name__)


class Status(Enum):
    # On the way to success
    USB_CONNECTED = "USB_CONNECTED"
    DISK_ENCRYPTED = "USB_ENCRYPTED"

    # Not too far from success
    USB_NOT_CONNECTED = "USB_NOT_CONNECTED"
    BAD_PASSPHRASE = "USB_BAD_PASSPHRASE"

    # Failure
    CALLED_PROCESS_ERROR = "CALLED_PROCESS_ERROR"
    DISK_ENCRYPTION_NOT_SUPPORTED_ERROR = "USB_ENCRYPTION_NOT_SUPPORTED"
    ERROR_USB_CONFIGURATION = "ERROR_USB_CONFIGURATION"
    UNEXPECTED_RETURN_STATUS = "UNEXPECTED_RETURN_STATUS"
    PRINTER_NOT_FOUND = "ERROR_PRINTER_NOT_FOUND"
    MISSING_PRINTER_URI = "ERROR_MISSING_PRINTER_URI"


class Error(Exception):
    def __init__(self, status: Status):
        self.status = status


class CLI:
    DISK_PRESENCE_CHECK_FN = "usb-test.sd-export"
    DISK_PRESENCE_CHECK_METADATA = {"device": "usb-test"}

    PRINTER_CHECK_FN = "printer-preflight.sd-export"
    PRINTER_CHECK_METADATA = {"device": "printer-preflight"}

    DISK_ENCRYPTION_CHECK_FN = "disk-test.sd-export"
    DISK_ENCRYPTION_CHECK_METADATA = {"device": "disk-test"}

    PRINT_FN = "print_archive.sd-export"
    PRINT_METADATA = {"device": "printer"}

    EXPORT_FN = "archive.sd-export"
    EXPORT_METADATA = {"device": "disk", "encryption_method": "luks"}
    DISK_ENCRYPTION_KEY_NAME = "encryption_key"

    def __init__(self) -> None:
        pass

    def check_printer_status(self, archive_dir: str) -> None:
        """
        Make sure printer is ready.
        """
        archive_path = Archive.create_archive(
            archive_dir, self.PRINTER_CHECK_FN, self.PRINTER_CHECK_METADATA
        )

        status = self._export_archive(archive_path)
        if status:
            raise Error(status)

    def export(self, archive_dir: str, filepaths: List[str], passphrase: str) -> None:
        """
        Run disk-test.

        Args:
            archive_dir (str): The path to the directory in which to create the archive.

        Raises:
            Error: Raised if the usb-test does not return a DISK_ENCRYPTED status.
        """
        metadata = self.EXPORT_METADATA.copy()
        metadata[self.DISK_ENCRYPTION_KEY_NAME] = passphrase
        archive_path = Archive.create_archive(archive_dir, self.EXPORT_FN, metadata, filepaths)

        status = self._export_archive(archive_path)
        if status:
            raise Error(status)  # pragma: no cover

    def check_disk_encryption(self, archive_dir: str) -> None:
        """
        Run disk-test.

        Args:
            archive_dir (str): The path to the directory in which to create the archive.

        Raises:
            Error: Raised if the usb-test does not return a DISK_ENCRYPTED status.
        """
        archive_path = Archive.create_archive(
            archive_dir, self.DISK_ENCRYPTION_CHECK_FN, self.DISK_ENCRYPTION_CHECK_METADATA
        )

        status = self._export_archive(archive_path)
        if status and status != Status.DISK_ENCRYPTED:
            raise Error(status)

    def print(self, archive_dir: str, filepaths: List[str]) -> None:
        """
        Create "printer" archive to send to Export VM.

        Args:
            archive_dir (str): The path to the directory in which to create the archive.

        """
        metadata = self.PRINT_METADATA.copy()
        archive_path = Archive.create_archive(archive_dir, self.PRINT_FN, metadata, filepaths)
        status = self._export_archive(archive_path)
        if status:
            raise Error(status)

    def check_disk_presence(self, archive_dir: str) -> None:
        """
        Run usb-test.

        Args:
            archive_dir (str): The path to the directory in which to create the archive.

        Raises:
            Error: Raised if the usb-test does not return a USB_CONNECTED status.
        """
        archive_path = Archive.create_archive(
            archive_dir, self.DISK_PRESENCE_CHECK_FN, self.DISK_PRESENCE_CHECK_METADATA
        )
        status = self._export_archive(archive_path)
        if status and status != Status.USB_CONNECTED:
            raise Error(status)

    @staticmethod
    def _export_archive(archive_path: str) -> Optional[Status]:
        """
        Make the subprocess call to send the archive to the Export VM, where the archive will be
        processed.

        Args:
            archive_path (str): The path to the archive to be processed.

        Returns:
            str: The export status returned from the Export VM processing script.

        Raises:
            Error: Raised if (1) CalledProcessError is encountered, which can occur when
                trying to start the Export VM when the USB device is not attached, or (2) when
                the return code from `check_output` is not 0.
        """
        try:
            # There are already talks of switching to a QVM-RPC implementation for unlocking devices
            # and exporting files, so it's important to remember to shell-escape what we pass to the
            # shell, even if for the time being we're already protected against shell injection via
            # Python's implementation of subprocess, see
            # https://docs.python.org/3/library/subprocess.html#security-considerations
            output = subprocess.check_output(
                [
                    quote("qrexec-client-vm"),
                    quote("--"),
                    quote("sd-devices"),
                    quote("qubes.OpenInVM"),
                    quote("/usr/lib/qubes/qopen-in-vm"),
                    quote("--view-only"),
                    quote("--"),
                    quote(archive_path),
                ],
                stderr=subprocess.STDOUT,
            )
            result = output.decode("utf-8").strip()

            # No status is returned for successful `disk`, `printer-test`, and `print` calls.
            # This will change in a future release of sd-export.
            if result:
                return Status(result)
            else:
                return None
        except ValueError as e:
            logger.debug(f"Export subprocess returned unexpected value: {e}")
            raise Error(Status.UNEXPECTED_RETURN_STATUS)
        except subprocess.CalledProcessError as e:
            logger.error("Subprocess failed")
            logger.debug(f"Subprocess failed: {e}")
            raise Error(Status.CALLED_PROCESS_ERROR)
