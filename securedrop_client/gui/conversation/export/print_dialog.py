from gettext import gettext as _
from typing import Optional

from PyQt5.QtCore import QSize, pyqtSignal, pyqtSlot

from securedrop_client.export import ExportStatus, Printer
from securedrop_client.gui.base import ModalDialog, SecureQLabel


class PrintDialog(ModalDialog):

    printer_status_check_requested = pyqtSignal()
    file_printing_requested = pyqtSignal(list)

    FILENAME_WIDTH_PX = 260

    def __init__(self, printer: Printer, file_location: str, file_name: str) -> None:
        super().__init__()

        self._printer = printer
        self.file_location = file_location
        self.file_name = SecureQLabel(
            file_name, wordwrap=False, max_length=self.FILENAME_WIDTH_PX
        ).text()
        # Hold onto the error status we receive from the Export VM
        self.error_status: Optional[ExportStatus] = None

        # Connect printer signals to slots
        self._printer.status_changed.connect(self._on_printer_status_changed)

        # Connect parent signals to slots
        self.continue_button.setEnabled(False)
        self.continue_button.clicked.connect(self.printer_status_check_requested)

        # Dialog content
        self.starting_header = _(
            "Preparing to print:<br />" '<span style="font-weight:normal">{}</span>'
        ).format(self.file_name)
        self.ready_header = _(
            "Ready to print:<br />" '<span style="font-weight:normal">{}</span>'
        ).format(self.file_name)
        self.insert_usb_header = _("Connect USB printer")
        self.error_header = _("Printing failed")
        self.starting_message = _(
            "<h2>Managing printout risks</h2>"
            "<b>QR codes and web addresses</b>"
            "<br />"
            "Never type in and open web addresses or scan QR codes contained in printed "
            "documents without taking security precautions. If you are unsure how to "
            "manage this risk, please contact your administrator."
            "<br /><br />"
            "<b>Printer dots</b>"
            "<br />"
            "Any part of a printed page may contain identifying information "
            "invisible to the naked eye, such as printer dots. Please carefully "
            "consider this risk when working with or publishing scanned printouts."
        )
        self.insert_usb_message = _("Please connect your printer to a USB port.")
        self.generic_error_message = _("See your administrator for help.")

        self._show_starting_instructions()
        self.start_animate_header()
        self._printer.check_status_once_on(self.printer_status_check_requested)
        self._printer.enqueue_job_on(self.file_printing_requested)
        self.printer_status_check_requested.emit()

    def text(self) -> str:
        return self.header.text() + super().text()

    def _show_starting_instructions(self) -> None:
        self.header.setText(self.starting_header)
        self.body.setText(self.starting_message)
        self.error_details.hide()
        self.adjustSize()

    def _show_insert_usb_message(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self.printer_status_check_requested)
        self.header.setText(self.insert_usb_header)
        self.body.setText(self.insert_usb_message)
        self.error_details.hide()
        self.adjustSize()

    def _show_generic_error_message(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self.close)
        self.continue_button.setText(_("DONE"))
        self.header.setText(self.error_header)
        self.body.setText(  # nosemgrep: semgrep.untranslated-gui-string
            "{}: {}".format(self.error_status, self.generic_error_message)
        )
        self.error_details.hide()
        self.adjustSize()

    @pyqtSlot()
    def _on_printer_status_changed(self) -> None:
        printer_status = self._printer.status
        if printer_status == Printer.StatusReady:
            self._on_print_preflight_check_succeeded()
        elif printer_status == Printer.StatusUnreachable:
            self._on_print_preflight_check_failed()
        else:
            # Printer.StatusUnknown is not supprted by this dialog.
            pass

    @pyqtSlot()
    def _print_file(self) -> None:
        self.file_printing_requested.emit([self.file_location])
        self.close()

    @pyqtSlot()
    def _on_print_preflight_check_succeeded(self) -> None:
        # If the continue button is disabled then this is the result of a background preflight check
        self.stop_animate_header()
        self.header_icon.update_image("printer.svg", svg_size=QSize(64, 64))
        self.header.setText(self.ready_header)
        if not self.continue_button.isEnabled():
            self.continue_button.clicked.disconnect()
            self.continue_button.clicked.connect(self._print_file)
            self.continue_button.setEnabled(True)
            self.continue_button.setFocus()
            return

        self._print_file()

    @pyqtSlot(object)
    def _on_print_preflight_check_failed(self) -> None:
        error = self._printer.last_error
        if error:
            status = error.status
        else:
            status = ExportStatus.UNEXPECTED_RETURN_STATUS

        self.stop_animate_header()
        self.header_icon.update_image("printer.svg", svg_size=QSize(64, 64))
        self.error_status = status
        # If the continue button is disabled then this is the result of a background preflight check
        if not self.continue_button.isEnabled():
            self.continue_button.clicked.disconnect()
            if status == ExportStatus.PRINTER_NOT_FOUND:
                self.continue_button.clicked.connect(self._show_insert_usb_message)
            else:
                self.continue_button.clicked.connect(self._show_generic_error_message)

            self.continue_button.setEnabled(True)
            self.continue_button.setFocus()
        else:
            if status == ExportStatus.PRINTER_NOT_FOUND:
                self._show_insert_usb_message()
            else:
                self._show_generic_error_message()
