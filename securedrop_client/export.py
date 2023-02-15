import json
import logging
import os
import subprocess
import tarfile
import threading
from enum import Enum
from io import BytesIO
from shlex import quote
from tempfile import TemporaryDirectory
from typing import List, Optional

from PyQt5.QtCore import QObject, pyqtBoundSignal, pyqtSignal, pyqtSlot

logger = logging.getLogger(__name__)


class ExportError(Exception):
    def __init__(self, status: "ExportStatus"):
        self.status: "ExportStatus" = status


class ExportStatus(Enum):
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


class Export(QObject):
    """
    This class sends files over to the Export VM so that they can be copied to a luks-encrypted USB
    disk drive or printed by a USB-connected printer.

    Files are archived in a specified format, which you can learn more about in the README for the
    securedrop-export repository.
    """

    METADATA_FN = "metadata.json"

    USB_TEST_FN = "usb-test.sd-export"
    USB_TEST_METADATA = {"device": "usb-test"}

    PRINTER_PREFLIGHT_FN = "printer-preflight.sd-export"
    PRINTER_PREFLIGHT_METADATA = {"device": "printer-preflight"}

    DISK_TEST_FN = "disk-test.sd-export"
    DISK_TEST_METADATA = {"device": "disk-test"}

    PRINT_FN = "print_archive.sd-export"
    PRINT_METADATA = {"device": "printer"}

    DISK_FN = "archive.sd-export"
    DISK_METADATA = {"device": "disk", "encryption_method": "luks"}
    DISK_ENCRYPTION_KEY_NAME = "encryption_key"
    DISK_EXPORT_DIR = "export_data"

    # Set up signals for communication with the controller
    preflight_check_call_failure = pyqtSignal(object)
    preflight_check_call_success = pyqtSignal()
    export_usb_call_failure = pyqtSignal(object)
    export_usb_call_success = pyqtSignal()
    export_completed = pyqtSignal(list)

    printer_preflight_success = pyqtSignal()
    printer_preflight_failure = pyqtSignal(object)
    print_call_failure = pyqtSignal(object)
    print_call_success = pyqtSignal()

    def __init__(
        self,
        export_preflight_check_requested: Optional[pyqtBoundSignal] = None,
        export_requested: Optional[pyqtBoundSignal] = None,
        print_preflight_check_requested: Optional[pyqtBoundSignal] = None,
        print_requested: Optional[pyqtBoundSignal] = None,
    ) -> None:
        super().__init__()

        self.connect_signals(
            export_preflight_check_requested,
            export_requested,
            print_preflight_check_requested,
            print_requested,
        )

    def connect_signals(
        self,
        export_preflight_check_requested: Optional[pyqtBoundSignal] = None,
        export_requested: Optional[pyqtBoundSignal] = None,
        print_preflight_check_requested: Optional[pyqtBoundSignal] = None,
        print_requested: Optional[pyqtBoundSignal] = None,
    ) -> None:

        # This instance can optionally react to events to prevent
        # coupling it to dependent code.
        if export_preflight_check_requested is not None:
            export_preflight_check_requested.connect(self.run_preflight_checks)
        if export_requested is not None:
            export_requested.connect(self.send_file_to_usb_device)
        if print_requested is not None:
            print_requested.connect(self.print)
        if print_preflight_check_requested is not None:
            print_preflight_check_requested.connect(self.run_printer_preflight)

    def _export_archive(cls, archive_path: str) -> Optional[ExportStatus]:
        """
        Make the subprocess call to send the archive to the Export VM, where the archive will be
        processed.

        Args:
            archive_path (str): The path to the archive to be processed.

        Returns:
            str: The export status returned from the Export VM processing script.

        Raises:
            ExportError: Raised if (1) CalledProcessError is encountered, which can occur when
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
                return ExportStatus(result)
            else:
                return None
        except ValueError as e:
            logger.debug(f"Export subprocess returned unexpected value: {e}")
            raise ExportError(ExportStatus.UNEXPECTED_RETURN_STATUS)
        except subprocess.CalledProcessError as e:
            logger.error("Subprocess failed")
            logger.debug(f"Subprocess failed: {e}")
            raise ExportError(ExportStatus.CALLED_PROCESS_ERROR)

    def _create_archive(
        cls, archive_dir: str, archive_fn: str, metadata: dict, filepaths: List[str] = []
    ) -> str:
        """
        Create the archive to be sent to the Export VM.

        Args:
            archive_dir (str): The path to the directory in which to create the archive.
            archive_fn (str): The name of the archive file.
            metadata (dict): The dictionary containing metadata to add to the archive.
            filepaths (List[str]): The list of files to add to the archive.

        Returns:
            str: The path to newly-created archive file.
        """
        archive_path = os.path.join(archive_dir, archive_fn)

        with tarfile.open(archive_path, "w:gz") as archive:
            cls._add_virtual_file_to_archive(archive, cls.METADATA_FN, metadata)

            needs_disambiguation = len(filepaths) > 1
            for filepath in filepaths:
                cls._add_file_to_archive(archive, filepath, disambiguate=needs_disambiguation)

        return archive_path

    def _add_virtual_file_to_archive(
        cls, archive: tarfile.TarFile, filename: str, filedata: dict
    ) -> None:
        """
        Add filedata to a stream of in-memory bytes and add these bytes to the archive.

        Args:
            archive (TarFile): The archive object to add the virtual file to.
            filename (str): The name of the virtual file.
            filedata (dict): The data to add to the bytes stream.

        """
        filedata_string = json.dumps(filedata)
        filedata_bytes = BytesIO(filedata_string.encode("utf-8"))
        tarinfo = tarfile.TarInfo(filename)
        tarinfo.size = len(filedata_string)
        archive.addfile(tarinfo, filedata_bytes)

    def _add_file_to_archive(
        cls, archive: tarfile.TarFile, filepath: str, disambiguate: bool = False
    ) -> None:
        """
        Add the file to the archive. When the archive is extracted, the file should exist in a
        directory called "export_data".

        Args:
            archive: The archive object ot add the file to.
            filepath: The path to the file that will be added to the supplied archive.
        """
        filename = os.path.basename(filepath)
        arcname = os.path.join(cls.DISK_EXPORT_DIR, filename)
        if disambiguate:
            (parent_path, _) = os.path.split(filepath)
            grand_parent_path, parent_name = os.path.split(parent_path)
            grand_parent_name = os.path.split(grand_parent_path)[1]
            arcname = os.path.join(grand_parent_name, parent_name, filename)
            if filename == "conversation.txt":
                arcname = os.path.join(parent_name, filename)

        archive.add(filepath, arcname=arcname, recursive=False)

    def _run_printer_preflight(self, archive_dir: str) -> None:
        """
        Make sure printer is ready.
        """
        archive_path = self._create_archive(
            archive_dir, self.PRINTER_PREFLIGHT_FN, self.PRINTER_PREFLIGHT_METADATA
        )

        status = self._export_archive(archive_path)
        if status:
            raise ExportError(status)

    def _run_usb_test(self, archive_dir: str) -> None:
        """
        Run usb-test.

        Args:
            archive_dir (str): The path to the directory in which to create the archive.

        Raises:
            ExportError: Raised if the usb-test does not return a USB_CONNECTED status.
        """
        archive_path = self._create_archive(archive_dir, self.USB_TEST_FN, self.USB_TEST_METADATA)
        status = self._export_archive(archive_path)
        if status and status != ExportStatus.USB_CONNECTED:
            raise ExportError(status)

    def _run_disk_test(self, archive_dir: str) -> None:
        """
        Run disk-test.

        Args:
            archive_dir (str): The path to the directory in which to create the archive.

        Raises:
            ExportError: Raised if the usb-test does not return a DISK_ENCRYPTED status.
        """
        archive_path = self._create_archive(archive_dir, self.DISK_TEST_FN, self.DISK_TEST_METADATA)

        status = self._export_archive(archive_path)
        if status and status != ExportStatus.DISK_ENCRYPTED:
            raise ExportError(status)

    def _run_disk_export(self, archive_dir: str, filepaths: List[str], passphrase: str) -> None:
        """
        Run disk-test.

        Args:
            archive_dir (str): The path to the directory in which to create the archive.

        Raises:
            ExportError: Raised if the usb-test does not return a DISK_ENCRYPTED status.
        """
        metadata = self.DISK_METADATA.copy()
        metadata[self.DISK_ENCRYPTION_KEY_NAME] = passphrase
        archive_path = self._create_archive(archive_dir, self.DISK_FN, metadata, filepaths)

        status = self._export_archive(archive_path)
        if status:
            raise ExportError(status)

    def _run_print(self, archive_dir: str, filepaths: List[str]) -> None:
        """
        Create "printer" archive to send to Export VM.

        Args:
            archive_dir (str): The path to the directory in which to create the archive.

        """
        metadata = self.PRINT_METADATA.copy()
        archive_path = self._create_archive(archive_dir, self.PRINT_FN, metadata, filepaths)
        status = self._export_archive(archive_path)
        if status:
            raise ExportError(status)

    @pyqtSlot()
    def run_preflight_checks(self) -> None:
        """
        Run preflight checks to verify that the usb device is connected and luks-encrypted.
        """
        with TemporaryDirectory() as temp_dir:
            try:
                logger.debug(
                    "beginning preflight checks in thread {}".format(
                        threading.current_thread().ident
                    )
                )
                self._run_usb_test(temp_dir)
                self._run_disk_test(temp_dir)
                logger.debug("completed preflight checks: success")
                self.preflight_check_call_success.emit()
            except ExportError as e:
                logger.debug("completed preflight checks: failure")
                self.preflight_check_call_failure.emit(e)

    @pyqtSlot()
    def run_printer_preflight(self) -> None:
        """
        Make sure the Export VM is started.
        """
        with TemporaryDirectory() as temp_dir:
            try:
                self._run_printer_preflight(temp_dir)
                self.printer_preflight_success.emit()
            except ExportError as e:
                logger.error("Export failed")
                logger.debug(f"Export failed: {e}")
                self.printer_preflight_failure.emit(e)

    @pyqtSlot(list, str)
    def send_file_to_usb_device(self, filepaths: List[str], passphrase: str) -> None:
        """
        Export the file to the luks-encrypted usb disk drive attached to the Export VM.

        Args:
            filepath: The path of file to export.
            passphrase: The passphrase to unlock the luks-encrypted usb disk drive.
        """
        with TemporaryDirectory() as temp_dir:
            try:
                logger.debug(
                    "beginning export from thread {}".format(threading.current_thread().ident)
                )
                self._run_disk_export(temp_dir, filepaths, passphrase)
                self.export_usb_call_success.emit()
                logger.debug("Export successful")
            except ExportError as e:
                logger.error("Export failed")
                logger.debug(f"Export failed: {e}")
                self.export_usb_call_failure.emit(e)

        self.export_completed.emit(filepaths)

    @pyqtSlot(list)
    def print(self, filepaths: List[str]) -> None:
        """
        Print the file to the printer attached to the Export VM.

        Args:
            filepath: The path of file to export.
        """
        with TemporaryDirectory() as temp_dir:
            try:
                logger.debug(
                    "beginning printer from thread {}".format(threading.current_thread().ident)
                )
                self._run_print(temp_dir, filepaths)
                self.print_call_success.emit()
                logger.debug("Print successful")
            except ExportError as e:
                logger.error("Export failed")
                logger.debug(f"Export failed: {e}")
                self.print_call_failure.emit(e)

        self.export_completed.emit(filepaths)


Service = Export

# Store a singleton service instance.
_service = Service()


def resetService() -> None:
    """Replaces the existing sngleton service instance by a new one.

    Get the instance by using getService().
    """
    global _service
    _service = Service()


def getService() -> Service:
    """All calls to this function return the same singleton service instance.

    Use resetService() to replace it by a new one."""
    return _service
