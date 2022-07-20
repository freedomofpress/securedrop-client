import logging
import os
from typing import Optional

from PyQt5.QtCore import QObject, QThread, pyqtSignal

from securedrop_client.export import Export
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

    def __init__(
        self, controller: Controller, export_service_thread: Optional[QThread] = None
    ) -> None:
        super().__init__()

        self._controller = controller

        self._export_service = Export(
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

        if export_service_thread is not None:
            # Run export object in a separate thread context (a reference to the
            # thread is kept on self such that it does not get garbage collected
            # after this method returns) - we want to keep our export thread around for
            # later processing.
            self._move_export_service_to_thread(export_service_thread)

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

    def _move_export_service_to_thread(self, thread: QThread) -> None:
        self._export_service_thread = thread

        self._export_service.moveToThread(self._export_service_thread)
        self._export_service_thread.start()


class StubDevice(QObject):
    """Abstracts an export service for use in GUI components.

    This class allows to emulate exports without side effects beyond the GUI.
    """

    export_preflight_check_succeeded = pyqtSignal()
    export_preflight_check_failed = pyqtSignal(object)  # only covered by functional test
    export_succeeded = pyqtSignal()
    export_failed = pyqtSignal(object)  # only covered by functional test

    print_preflight_check_succeeded = pyqtSignal()
    print_preflight_check_failed = pyqtSignal(object)  # only covered by integration test

    def __init__(
        self, controller: Controller, export_service_thread: Optional[QThread] = None
    ) -> None:
        super().__init__()

        self._controller = controller

    def run_printer_preflight_checks(self) -> None:
        """
        Run preflight checks to make sure the Export VM is configured correctly.
        """
        logger.info("Running printer preflight check")

        self.print_preflight_check_succeeded.emit()

    def run_export_preflight_checks(self) -> None:
        """
        Run preflight checks to make sure the Export VM is configured correctly.
        """
        logger.info("Running export preflight check")

        self.export_preflight_check_succeeded.emit()

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

        self.export_succeeded.emit()

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

        pass
