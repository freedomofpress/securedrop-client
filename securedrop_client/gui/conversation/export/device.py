import logging
import os

from PyQt5.QtCore import QObject, pyqtSignal

from securedrop_client import export
from securedrop_client.logic import Controller

logger = logging.getLogger(__name__)


class Device(QObject):
    """Abstracts an export service for use in GUI components.

    This class defines an interface for GUI components to have access
    to the status of an export device without needed to interact directly
    with the underlying export service.
    """

    export_preflight_check_requested = pyqtSignal()
    export_preflight_check_succeeded = pyqtSignal()
    export_preflight_check_failed = pyqtSignal(object)

    export_requested = pyqtSignal(list, str)
    export_succeeded = pyqtSignal()
    export_failed = pyqtSignal(object)
    export_completed = pyqtSignal(list)

    print_preflight_check_requested = pyqtSignal()
    print_preflight_check_succeeded = pyqtSignal()
    print_preflight_check_failed = pyqtSignal(object)

    print_requested = pyqtSignal(list)
    print_succeeded = pyqtSignal()
    print_failed = pyqtSignal(object)

    def __init__(self, controller: Controller, export_service: export.Service) -> None:
        super().__init__()

        self._controller = controller
        self._export_service = export_service

        self._export_service.connect_signals(
            self.export_preflight_check_requested,
            self.export_requested,
            self.print_preflight_check_requested,
            self.print_requested,
        )

        # Abstract the Export instance away from the GUI
        self._export_service.preflight_check_call_success.connect(
            self.export_preflight_check_succeeded
        )
        self._export_service.preflight_check_call_failure.connect(
            self.export_preflight_check_failed
        )

        self._export_service.export_usb_call_success.connect(self.export_succeeded)
        self._export_service.export_usb_call_failure.connect(self.export_failed)
        self._export_service.export_completed.connect(self.export_completed)

        self._export_service.printer_preflight_success.connect(self.print_preflight_check_succeeded)
        self._export_service.printer_preflight_failure.connect(self.print_preflight_check_failed)

        self._export_service.print_call_failure.connect(self.print_failed)
        self._export_service.print_call_success.connect(self.print_succeeded)

    def run_printer_preflight_checks(self) -> None:
        """
        Run preflight checks to make sure the Export VM is configured correctly.
        """
        logger.info("Running printer preflight check")
        self.print_preflight_check_requested.emit()

    def run_export_preflight_checks(self) -> None:
        """
        Run preflight checks to make sure the Export VM is configured correctly.
        """
        logger.info("Running export preflight check")
        self.export_preflight_check_requested.emit()

    def export_file_to_usb_drive(self, file_uuid: str, passphrase: str) -> None:
        """
        Send the file specified by file_uuid to the Export VM with the user-provided passphrase for
        unlocking the attached transfer device.  If the file is missing, update the db so that
        is_downloaded is set to False.
        """
        file = self._controller.get_file(file_uuid)
        file_location = file.location(self._controller.data_dir)
        logger.info("Exporting file in: {}".format(os.path.dirname(file_location)))

        if not self._controller.downloaded_file_exists(file):
            return

        self.export_requested.emit([file_location], passphrase)

    def print_file(self, file_uuid: str) -> None:
        """
        Send the file specified by file_uuid to the Export VM. If the file is missing, update the db
        so that is_downloaded is set to False.
        """
        file = self._controller.get_file(file_uuid)
        file_location = file.location(self._controller.data_dir)
        logger.info("Printing file in: {}".format(os.path.dirname(file_location)))

        if not self._controller.downloaded_file_exists(file):
            return

        self.print_requested.emit([file_location])
