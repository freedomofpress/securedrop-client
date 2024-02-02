import json
import logging
import os
import subprocess
import tarfile
from io import BytesIO
from shlex import quote
from tempfile import TemporaryDirectory
from typing import List, Optional

from PyQt5.QtCore import QObject, pyqtSignal

from securedrop_client.export_status import ExportError, ExportStatus

logger = logging.getLogger(__name__)


class Export(QObject):
    """
    Interface for sending files to Export VM for transfer to a
    disk drive or printed by a USB-connected printer.

    Files are archived in a specified format, (see `export` README).

    A list of valid filepaths must be supplied.
    """

    _METADATA_FN = "metadata.json"

    _USB_TEST_FN = "usb-test.sd-export"
    _USB_TEST_METADATA = {"device": "usb-test"}

    _PRINTER_PREFLIGHT_FN = "printer-preflight.sd-export"
    _PRINTER_PREFLIGHT_METADATA = {"device": "printer-preflight"}

    _PRINT_FN = "print_archive.sd-export"
    _PRINT_METADATA = {"device": "printer"}

    _DISK_FN = "archive.sd-export"
    _DISK_METADATA = {"device": "disk"}
    _DISK_ENCRYPTION_KEY_NAME = "encryption_key"
    _DISK_EXPORT_DIR = "export_data"

    # New, replacement for export success and error statuses
    export_state_changed = pyqtSignal(object)

    # Emit ExportStatus
    export_preflight_check_succeeded = pyqtSignal(object)
    export_succeeded = pyqtSignal(object)

    print_preflight_check_succeeded = pyqtSignal(object)
    print_succeeded = pyqtSignal(object)

    # Used for both print and export
    export_completed = pyqtSignal(object)

    # Emit ExportError(status=ExportStatus)
    export_preflight_check_failed = pyqtSignal(object)
    export_failed = pyqtSignal(object)

    print_preflight_check_failed = pyqtSignal(object)
    print_failed = pyqtSignal(object)

    def run_printer_preflight_checks(self) -> None:
        """
        Make sure the Export VM is started.
        """
        logger.info("Beginning printer preflight check")
        try:
            with TemporaryDirectory() as tmp_dir:
                archive_path = self._create_archive(
                    archive_dir=tmp_dir,
                    archive_fn=self._PRINTER_PREFLIGHT_FN,
                    metadata=self._PRINTER_PREFLIGHT_METADATA,
                )
                status = self._run_qrexec_export(archive_path)
                self.print_preflight_check_succeeded.emit(status)
        except ExportError as e:
            logger.error("Print preflight failed")
            logger.debug(f"Print preflight failed: {e}")
            self.print_preflight_check_failed.emit(e)

    def run_export_preflight_checks(self) -> None:
        """
        Run preflight check to verify that a valid USB device is connected.
        """
        try:
            logger.debug("Beginning export preflight check")

            with TemporaryDirectory() as tmp_dir:
                archive_path = self._create_archive(
                    archive_dir=tmp_dir,
                    archive_fn=self._USB_TEST_FN,
                    metadata=self._USB_TEST_METADATA,
                )
                status = self._run_qrexec_export(archive_path)
                self.export_preflight_check_succeeded.emit(status)

        except ExportError as e:
            logger.error("Export preflight failed")
            self.export_preflight_check_failed.emit(e)

            if e.status:
                self.export_state_changed.emit(e.status)
            else:
                logger.error("ExportError, no status supplied")
                # Emit a generic error
                self.export_state_changed.emit(ExportStatus.ERROR_EXPORT)

    def export(self, filepaths: List[str], passphrase: Optional[str]) -> None:
        """
        Bundle filepaths into a tarball and send to encrypted USB via qrexec,
        optionally supplying a passphrase to unlock encrypted drives.
        """
        try:
            logger.debug(f"Begin exporting {len(filepaths)} item(s)")

            # Edit metadata template to include passphrase
            metadata = self._DISK_METADATA.copy()
            if passphrase:
                metadata[self._DISK_ENCRYPTION_KEY_NAME] = passphrase

            with TemporaryDirectory() as tmp_dir:
                archive_path = self._create_archive(
                    archive_dir=tmp_dir,
                    archive_fn=self._DISK_FN,
                    metadata=metadata,
                    filepaths=filepaths,
                )
                status = self._run_qrexec_export(archive_path)
                self.export_state_changed.emit(status)

                self.export_succeeded.emit(status)
                logger.debug(f"Status {status}")

        except ExportError as e:
            logger.error("Export failed")
            logger.debug(f"Export failed: {e}")
            self.export_failed.emit(e)

            if e.status and isinstance(e.status, ExportStatus):
                self.export_state_changed.emit(e.status)
            else:
                logger.error("ExportError, no status supplied")
                # Emit a generic error
                self.export_state_changed.emit(ExportStatus.ERROR_EXPORT)

        self.export_completed.emit(filepaths)

    def print(self, filepaths: List[str]) -> None:
        """
        Bundle files at self._filepaths_list into tarball and send for
        printing via qrexec.
        """
        try:
            logger.debug("Beginning print")

            with TemporaryDirectory() as tmp_dir:
                archive_path = self._create_archive(
                    archive_dir=tmp_dir,
                    archive_fn=self._PRINT_FN,
                    metadata=self._PRINT_METADATA,
                    filepaths=filepaths,
                )
                status = self._run_qrexec_export(archive_path)
                self.print_succeeded.emit(status)
                logger.debug(f"Status {status}")

        except ExportError as e:
            logger.error("Export failed")
            logger.debug(f"Export failed: {e}")
            self.print_failed.emit(e)

        self.export_completed.emit(filepaths)

    def _run_qrexec_export(self, archive_path: str) -> ExportStatus:
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
            if result:

                # This is a bit messy, but make sure we are just taking the last line
                # (no-op if no newline)
                status_string = result.split("\n")[-1]
                return ExportStatus(status_string)
            else:
                logger.error("Export subprocess did not return a value we could parse")
                raise ExportError(ExportStatus.UNEXPECTED_RETURN_STATUS)

        except ValueError as e:
            logger.debug(f"Export subprocess returned unexpected value: {e}")
            raise ExportError(ExportStatus.UNEXPECTED_RETURN_STATUS)
        except subprocess.CalledProcessError as e:
            logger.error("Subprocess failed")
            logger.debug(f"Subprocess failed: {e}")
            raise ExportError(ExportStatus.CALLED_PROCESS_ERROR)

    def _create_archive(
        self, archive_dir: str, archive_fn: str, metadata: dict, filepaths: List[str] = []
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
            self._add_virtual_file_to_archive(archive, self._METADATA_FN, metadata)

            # When more than one file is added to the archive,
            # extra care must be taken to prevent name collisions.
            is_one_of_multiple_files = len(filepaths) > 1
            missing_count = 0
            for filepath in filepaths:
                if not (os.path.exists(filepath)):
                    missing_count += 1
                    logger.debug(
                        f"'{filepath}' does not exist, and will not be included in archive"
                    )
                    # Controller checks files and keeps a reference open during export,
                    # so this shouldn't be reachable
                    logger.warning("File not found at specified filepath, skipping")
                else:
                    self._add_file_to_archive(
                        archive, filepath, prevent_name_collisions=is_one_of_multiple_files
                    )
            if missing_count == len(filepaths) and missing_count > 0:
                # Context manager will delete archive even if an exception occurs
                # since the archive is in a TemporaryDirectory
                logger.error("Files were moved or missing")
                raise ExportError(ExportStatus.ERROR_MISSING_FILES)

        return archive_path

    def _add_virtual_file_to_archive(
        self, archive: tarfile.TarFile, filename: str, filedata: dict
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
        self, archive: tarfile.TarFile, filepath: str, prevent_name_collisions: bool = False
    ) -> None:
        """
        Add the file to the archive. When the archive is extracted, the file should exist in a
        directory called "export_data".

        Args:
            archive: The archive object ot add the file to.
            filepath: The path to the file that will be added to the supplied archive.
        """
        filename = os.path.basename(filepath)
        arcname = os.path.join(self._DISK_EXPORT_DIR, filename)
        if prevent_name_collisions:
            (parent_path, _) = os.path.split(filepath)
            grand_parent_path, parent_name = os.path.split(parent_path)
            grand_parent_name = os.path.split(grand_parent_path)[1]
            arcname = os.path.join("export_data", grand_parent_name, parent_name, filename)
            if filename == "transcript.txt":
                arcname = os.path.join("export_data", parent_name, filename)

        archive.add(filepath, arcname=arcname, recursive=False)
