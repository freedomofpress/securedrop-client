import json
import logging
import os
import subprocess
import tarfile
import threading
from io import BytesIO
from shlex import quote
from tempfile import TemporaryDirectory
from typing import List, Optional

from PyQt5.QtCore import QObject, pyqtBoundSignal, pyqtSignal, pyqtSlot

from securedrop_client.export_status import ExportStatus

logger = logging.getLogger(__name__)


class ExportError(Exception):
    def __init__(self, status: "ExportStatus"):
        self.status: "ExportStatus" = status


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

    DISK_METADATA = {"device": "disk"}
    DISK_ENCRYPTION_KEY_NAME = "encryption_key"
    DISK_EXPORT_DIR = "export_data"

    # Set up signals for communication with the controller #
    # Emit ExportStatus
    preflight_check_call_success = pyqtSignal(object)
    export_usb_call_success = pyqtSignal(object)
    printer_preflight_success = pyqtSignal(object)
    print_call_success = pyqtSignal(object)

    # Emit ExportError(status=ExportStatus)
    export_usb_call_failure = pyqtSignal(object)
    preflight_check_call_failure = pyqtSignal(object)
    printer_preflight_failure = pyqtSignal(object)
    print_call_failure = pyqtSignal(object)

    # Emit List[str] of filepaths
    export_completed = pyqtSignal(list)

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

    def _run_qrexec_export(cls, archive_path: str) -> ExportStatus:
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

            return ExportStatus(result)

        except ValueError as e:
            logger.debug(f"Export subprocess returned unexpected value: {e}")
            raise ExportError(ExportStatus.UNEXPECTED_RETURN_STATUS)
        except subprocess.CalledProcessError as e:
            logger.error("Subprocess failed")
            logger.debug(f"Subprocess failed: {e}")
            raise ExportError(ExportStatus.CALLED_PROCESS_ERROR)

    def _create_archive(
        cls, archive_dir: str, archive_fn: str, metadata: dict, filepaths: List[str]
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

            # When more than one file is added to the archive,
            # extra care must be taken to prevent name collisions.
            is_one_of_multiple_files = len(filepaths) > 1
            for filepath in filepaths:
                cls._add_file_to_archive(
                    archive, filepath, prevent_name_collisions=is_one_of_multiple_files
                )

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
        cls, archive: tarfile.TarFile, filepath: str, prevent_name_collisions: bool = False
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
        if prevent_name_collisions:
            (parent_path, _) = os.path.split(filepath)
            grand_parent_path, parent_name = os.path.split(parent_path)
            grand_parent_name = os.path.split(grand_parent_path)[1]
            arcname = os.path.join("export_data", grand_parent_name, parent_name, filename)
            if filename == "transcript.txt":
                arcname = os.path.join("export_data", parent_name, filename)

        archive.add(filepath, arcname=arcname, recursive=False)

    def _build_archive_and_export(
        self, metadata: dict, filename: str, filepaths: List[str] = []
    ) -> ExportStatus:
        """
        Build archive, run qrexec command and return resulting ExportStatus.

        ExportError may be raised during underlying _run_qrexec_export call,
        and is handled by the calling method.
        """
        with TemporaryDirectory() as tmp_dir:
            archive_path = self._create_archive(
                archive_dir=tmp_dir, archive_fn=filename, metadata=metadata, filepaths=filepaths
            )
            return self._run_qrexec_export(archive_path)

    @pyqtSlot()
    def run_preflight_checks(self) -> None:
        """
        Run preflight checks to verify that a valid USB device is connected.
        """
        try:
            logger.debug(
                "beginning preflight checks in thread {}".format(threading.current_thread().ident)
            )

            status = self._build_archive_and_export(
                metadata=self.USB_TEST_METADATA, filename=self.USB_TEST_FN
            )

            logger.debug(f"Preflight check result: {status.value}")

            if status in [ExportStatus.DEVICE_LOCKED, ExportStatus.DEVICE_WRITABLE]:
                self.preflight_check_call_success.emit(status)
            else:
                # These are error states, or at least, they require the user
                # to behave differently. In future we should probably not
                # emit different signals for "success" and "error"
                # and just emit one signal and let the UI decide how
                # to handle it.
                self.preflight_check_call_failure.emit(ExportError(status=status))
        except ExportError as e:
            logger.debug("completed preflight checks: failure")
            self.preflight_check_call_failure.emit(e)

    @pyqtSlot()
    def run_printer_preflight(self) -> None:
        """
        Make sure the Export VM is started.
        """
        try:
            status = self._build_archive_and_export(
                metadata=self.PRINTER_PREFLIGHT_METADATA, filename=self.PRINTER_PREFLIGHT_FN
            )
            self.printer_preflight_success.emit(status)
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
        try:
            logger.debug("beginning export from thread {}".format(threading.current_thread().ident))
            # Edit metadata template to include passphrase
            metadata = self.DISK_METADATA.copy()
            metadata[self.DISK_ENCRYPTION_KEY_NAME] = passphrase
            status = self._build_archive_and_export(
                metadata=metadata, filename=self.DISK_FN, filepaths=filepaths
            )

            self.export_usb_call_success.emit(status)
            logger.debug(f"Status {status}")
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
        try:
            logger.debug(
                "beginning printer from thread {}".format(threading.current_thread().ident)
            )
            status = self._build_archive_and_export(
                metadata=self.PRINT_METADATA, filename=self.PRINT_FN, filepaths=filepaths
            )
            self.print_call_success.emit(status)
            logger.debug(f"Status {status}")
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
