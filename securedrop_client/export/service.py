import logging
import threading
from tempfile import TemporaryDirectory
from typing import List, Optional

from PyQt5.QtCore import QObject, pyqtSignal, pyqtSlot

from .cli import CLI
from .cli import Error as CLIError

logger = logging.getLogger(__name__)


class Service(QObject):
    """
    This class sends files over to the Export VM so that they can be copied to a luks-encrypted USB
    disk drive or printed by a USB-connected printer.

    Files are archived in a specified format, which you can learn more about in the README for the
    securedrop-export repository.
    """

    # Set up signals for communication with the export device
    preflight_check_call_failure = pyqtSignal(object)  # DEPRECATED
    preflight_check_call_success = pyqtSignal()  # DEPRECATED
    export_usb_call_failure = pyqtSignal(object)  # DEPRECATED
    export_usb_call_success = pyqtSignal()  # DEPRECATED
    export_completed = pyqtSignal(list)  # DEPRECATED

    printer_preflight_success = pyqtSignal()  # DEPRECATED
    printer_preflight_failure = pyqtSignal(object)  # DEPRECATED
    print_call_failure = pyqtSignal(object)  # DEPRECATED
    print_call_success = pyqtSignal()  # DEPRECATED

    luks_encrypted_disk_not_found = pyqtSignal(object)
    luks_encrypted_disk_found = pyqtSignal()
    export_failed = pyqtSignal(object)
    export_succeeded = pyqtSignal()
    export_finished = pyqtSignal(list)

    printer_found_ready = pyqtSignal()
    printer_not_found_ready = pyqtSignal(object)
    print_failed = pyqtSignal(object)
    print_succeeded = pyqtSignal()

    def __init__(
        self,
        disk_check_requested: Optional[pyqtSignal] = None,
        export_requested: Optional[pyqtSignal] = None,
        printer_check_requested: Optional[pyqtSignal] = None,
        print_requested: Optional[pyqtSignal] = None,
    ) -> None:
        super().__init__()

        self._cli = CLI()

        self.connect_signals(
            disk_check_requested,
            export_requested,
            printer_check_requested,
            print_requested,
        )

        # Ensure backwards compatibility with deprecated API
        self.printer_found_ready.connect(self.printer_preflight_success)
        self.printer_not_found_ready.connect(self.printer_preflight_failure)
        self.print_succeeded.connect(self.print_call_success)
        self.print_failed.connect(self.print_call_failure)

        self.luks_encrypted_disk_found.connect(self.preflight_check_call_success)
        self.luks_encrypted_disk_not_found.connect(self.preflight_check_call_failure)
        self.export_succeeded.connect(self.export_usb_call_success)
        self.export_failed.connect(self.export_usb_call_failure)
        self.export_finished.connect(self.export_completed)

    def connect_signals(
        self,
        disk_check_requested: Optional[pyqtSignal] = None,
        export_requested: Optional[pyqtSignal] = None,
        printer_check_requested: Optional[pyqtSignal] = None,
        print_requested: Optional[pyqtSignal] = None,
    ) -> None:

        # This instance can optionally react to events to prevent
        # coupling it to dependent code.
        if disk_check_requested is not None:
            disk_check_requested.connect(self.check_disk)
        if export_requested is not None:
            export_requested.connect(self.export)
        if print_requested is not None:
            print_requested.connect(self.print)
        if printer_check_requested is not None:
            printer_check_requested.connect(self.check_printer_status)

    @pyqtSlot()
    def check_disk(self) -> None:
        """
        Checks that the USB disk is connected and LUKS-encrypted.
        """
        with TemporaryDirectory() as temp_dir:
            try:
                logger.debug(
                    "beginning preflight checks in thread {}".format(
                        threading.current_thread().ident
                    )
                )
                self._cli.check_disk_presence(temp_dir)
                self._cli.check_disk_encryption(temp_dir)
                logger.debug("completed preflight checks: success")
                self.luks_encrypted_disk_found.emit()
            except CLIError as e:
                logger.debug("completed preflight checks: failure")
                self.luks_encrypted_disk_not_found.emit(e)

    @pyqtSlot()
    def check_printer_status(self) -> None:
        """
        Make sure the Export VM is started.
        """
        with TemporaryDirectory() as temp_dir:
            try:
                self._cli.check_printer_status(temp_dir)
                self.printer_found_ready.emit()
            except CLIError as e:
                logger.error("Export failed")
                logger.debug(f"Export failed: {e}")
                self.printer_not_found_ready.emit(e)

    @pyqtSlot(list, str)
    def export(self, filepaths: List[str], passphrase: str) -> None:
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
                self._cli.export(temp_dir, filepaths, passphrase)
                self.export_succeeded.emit()
                logger.debug("Export successful")
            except CLIError as e:
                logger.error("Export failed")
                logger.debug(f"Export failed: {e}")
                self.export_failed.emit(e)

        self.export_finished.emit(filepaths)

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
                self._cli.print(temp_dir, filepaths)
                self.print_succeeded.emit()
                logger.debug("Print successful")
            except CLIError as e:
                logger.error("Export failed")
                logger.debug(f"Export failed: {e}")
                self.print_failed.emit(e)

        self.export_completed.emit(filepaths)


# Store the service instance to prevent unnecessary concurrent access to the CLI. See getService.
_service = Service()


def getService() -> Service:
    """All calls to this function return the same service instance."""
    return _service
