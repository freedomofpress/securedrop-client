import json
import logging
import os
import tarfile
from io import BytesIO
from shlex import quote
from tempfile import TemporaryDirectory
from typing import Callable, List, Optional

from PyQt5.QtCore import QProcess, QObject, pyqtSignal

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

    # Emit export states
    export_state_changed = pyqtSignal(object)

    # Emit print states
    print_preflight_check_succeeded = pyqtSignal(object)
    print_succeeded = pyqtSignal(object)

    export_completed = pyqtSignal(object)

    print_preflight_check_failed = pyqtSignal(object)
    print_failed = pyqtSignal(object)

    process = None  # Optional[QProcess]

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
                self._run_qrexec_export(
                    archive_path, self._on_print_preflight_success, self._on_print_prefight_error
                )
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
                # Emits status via on_process_completed()
                self._run_qrexec_export(
                    archive_path, self._on_export_process_finished, self._on_export_process_error
                )

        except ExportError as e:
            logger.error("Export preflight failed")

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

                # Emits status through callbacks
                self._run_qrexec_export(
                    archive_path, self._on_export_process_finished, self._on_export_process_error
                )

        except IOError as e:
            logger.error("Export failed")
            logger.debug(f"Export failed: {e}")
            self.export_state_changed.emit(ExportStatus.ERROR_EXPORT)

    def _run_qrexec_export(
        self, archive_path: str, success_callback: Callable, error_callback: Callable
    ) -> None:
        """
        Send the archive to the Export VM, where the archive will be processed.
        Uses qrexec-client-vm (via QProcess). Results are emitted via the
        `on_process_finished` callback; errors are reported via `on_process_error`.

        Args:
            archive_path (str): The path to the archive to be processed.
            success_callback, err_callback: Callback functions to connect to the success and
            error signals of QProcess. They are included to accommodate the print functions,
            which still use separate signals for print preflight, print, and error states, but
            can be removed in favour of a generic success callback and error callback when the
            print code is updated.

        Returns:
            str: The export status returned from the Export VM processing script.

        Raises:
            ExportError: Raised if (1) CalledProcessError is encountered, which can occur when
                trying to start the Export VM when the USB device is not attached, or (2) when
                the return code from `check_output` is not 0.
        """
        logger.debug(f"Preparing to open {archive_path} in sd-devices...")

        # There are already talks of switching to a QVM-RPC implementation for unlocking devices
        # and exporting files, so it's important to remember to shell-escape what we pass to the
        # shell, even if for the time being we're already protected against shell injection via
        # Python's implementation of subprocess, see
        # https://docs.python.org/3/library/subprocess.html#security-considerations
        qrexec = "/usr/bin/qrexec-client-vm"
        args = [
            quote("--"),
            quote("sd-devices"),
            quote("qubes.OpenInVM"),
            quote("/usr/lib/qubes/qopen-in-vm"),
            quote("--view-only"),
            quote("--"),
            quote(archive_path),
        ]

        self.process = QProcess()
        # self.process.readyReadStandardError.connect(success_callback)

        self.process.finished.connect(success_callback)
        self.process.errorOccurred.connect(error_callback)

        self.process.start(qrexec, args)

    def _on_export_process_finished(self):
        """
        Callback to handle and emit QProcess results. Method signature
        cannot change.
        """
        out = self.process.readAllStandardOutput().data().decode("utf-8")

        # securedrop-export writes status to stderr
        err = self.process.readAllStandardError()

        logger.debug(f"stdout: {out}")
        logger.debug(f"stderr: {err}")

        try:
            result = err.data().decode("utf-8").strip()
            if result:
                logger.debug(f"Result is {result}")
                # This is a bit messy, but make sure we are just taking the last line
                # (no-op if no newline, since we already stripped whitespace above)
                status_string = result.split("\n")[-1]
                self.export_state_changed.emit(ExportStatus(status_string))

            else:
                logger.error("Export subprocess did not return a value we could parse")
                self.export_state_changed.emit(ExportStatus.UNEXPECTED_RETURN_STATUS)

        except ValueError as e:
            logger.debug(f"Export subprocess returned unexpected value: {e}")
            self.export_state_changed.emit(ExportStatus.UNEXPECTED_RETURN_STATUS)

    def _on_export_process_error(self):
        """
        Callback, called if QProcess cannot complete. Method signature
        cannot change.
        """
        err = self.process.readAllStandardError().data().decode("utf-8")

        logger.error(f"Export process error: {err}")
        self.export_state_changed.emit(ExportStatus.CALLED_PROCESS_ERROR)

    def _on_print_preflight_success(self):
        logger.debug("Print preflight success")
        self.print_preflight_check_succeeded.emit()

    def _on_print_prefight_error(self):
        logger.debug("Print preflight error")
        self.print_preflight_check_failed.emit(ExportStatus.PRINT_PREFLIGHT_SUCCESS)

    # Todo: not sure if we need to connect here, since the print dialog is managed by sd-devices.
    # We can probably use the export callback.
    def _on_print_sucess(self):
        logger.debug("Print success")
        self.print_succeeded.emit(ExportStatus.PRINT_SUCCESS)
        self.export_completed.emit()

    def end_process(self) -> None:
        logger.debug("Terminate process")
        if self.process is not None and not self.process.waitForFinished(50):
            self.process.terminate()

    def _on_print_error(self):
        # securedrop-export writes status to stderr
        err = self.process.readAllStandardError()
        logger.debug(f"Print error: {err}")

        try:
            result = err.data().decode("utf-8").strip()
            if result:
                logger.debug(f"Result is {result}")
                status = ExportStatus(result)
                self.print_failed.emit(ExportError(status))
            else:
                logger.error("Print error, but no value we could parse")
                self.print_failed.emit(ExportStatus.ERROR_PRINT)

        except ValueError as e:
            logger.debug(f"Export subprocess returned unexpected value: {e}")
            self.print_failed.emit(ExportError(ExportStatus.ERROR_PRINT))

    def print(self, filepaths: List[str]) -> None:
        """
        Bundle files at filepaths into tarball and send for
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
                self._run_qrexec_export(archive_path, self._on_print_sucess, self._on_print_error)

        except IOError as e:
            logger.error("Export failed")
            logger.debug(f"Export failed: {e}")
            self.print_failed.emit(e)

        self.export_completed.emit(filepaths)

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
