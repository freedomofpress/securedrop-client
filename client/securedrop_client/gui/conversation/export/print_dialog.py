from gettext import gettext as _

from PyQt5.QtCore import QSize, pyqtSlot

from securedrop_client.export_status import ExportStatus
from securedrop_client.gui.base import ModalDialog, SecureQLabel

from ....export import Export


class PrintDialog(ModalDialog):
    FILENAME_WIDTH_PX = 260

    def __init__(self, device: Export, file_name: str, filepaths: list[str]) -> None:
        super().__init__()

        self._device = device
        self.filepaths = filepaths
        self.file_name = SecureQLabel(
            file_name, wordwrap=False, max_length=self.FILENAME_WIDTH_PX
        ).text()

        # Hold onto the error status we receive from the Export VM. Only required
        # because we're reusing the same modal dialog with different text depending
        # on conditions, and need to pass methods to Qt handlers with a predefined
        # message signature.
        self.status: ExportStatus | None = None

        # Connect device signals to slots
        self._device.print_preflight_check_succeeded.connect(
            self._on_print_preflight_check_succeeded
        )
        self._device.print_preflight_check_failed.connect(self._on_print_preflight_check_failed)

        # For now, connect both success and error signals to close the print dialog.
        self._device.print_succeeded.connect(self._on_print_complete)
        self._device.print_failed.connect(self._on_print_complete)

        # Connect parent signals to slots
        self.continue_button.setEnabled(False)
        self.continue_button.clicked.connect(self._run_preflight)

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
        self.unprintable_type_error_message = _("This file type cannot be printed.")

        self._show_starting_instructions()
        self.start_animate_header()
        self._run_preflight()

    def _show_starting_instructions(self) -> None:
        self.header.setText(self.starting_header)
        self.body.setText(self.starting_message)
        self.error_details.hide()
        self.adjustSize()

    def _show_insert_usb_message(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self._run_preflight)
        self.header.setText(self.insert_usb_header)
        self.body.setText(self.insert_usb_message)
        self.error_details.hide()
        self.adjustSize()

    def _show_unprintable_message(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self.close)
        self.header.setText(self.error_header)
        self.body.setText(self.unprintable_type_error_message)
        self.error_details.hide()
        self.adjustSize()

    def _show_generic_error_message(self) -> None:
        self._show_error_message()

    def _show_error_message(self) -> None:
        """
        Show error message based on ExportStatus returned.
        """
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self.close)
        self.continue_button.setText(_("DONE"))
        self.header.setText(self.error_header)
        if self.status == ExportStatus.ERROR_UNPRINTABLE_TYPE:
            body_text = self.unprintable_type_error_message
        else:
            body_text = self.generic_error_message

        if self.status:
            self.body.setText(  # nosemgrep: semgrep.untranslated-gui-string
                f"{self.status.value}: {body_text}"
            )
        else:
            self.body.setText(  # nosemgrep: semgrep.untranslated-gui-string
                body_text
            )
        self.error_details.hide()
        self.adjustSize()

    @pyqtSlot()
    def _run_preflight(self) -> None:
        self._device.run_printer_preflight_checks()

    @pyqtSlot()
    def _print_file(self) -> None:
        self.start_animate_activestate()
        self._device.print(self.filepaths)

    @pyqtSlot(object)
    def _on_print_complete(self, status: ExportStatus) -> None:
        """
        Send a signal to close the print dialog or display
        an appropriate error message.
        """
        self.status = status
        self.stop_animate_activestate()
        if status == ExportStatus.PRINT_SUCCESS:
            self.close()
        elif self.status == ExportStatus.ERROR_PRINTER_NOT_FOUND:
            self._show_insert_usb_message()
        elif self.status == ExportStatus.ERROR_UNPRINTABLE_TYPE:
            self._show_unprintable_message()
        else:
            self._show_error_message()

    @pyqtSlot(object)
    def _on_print_preflight_check_succeeded(self, status: ExportStatus) -> None:
        # We don't use the ExportStatus for now for "success" status,
        # but in future work we will migrate towards a wizard-style dialog, where
        # success and intermediate status values all use the same PyQt slot.
        # If the continue button is disabled then this is the result of a background preflight check
        self.status = status
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
    def _on_print_preflight_check_failed(self, status: ExportStatus) -> None:
        self.status = status
        self.stop_animate_header()
        self.header_icon.update_image("printer.svg", svg_size=QSize(64, 64))
        # If the continue button is disabled then this is the result of a background preflight check
        if not self.continue_button.isEnabled():
            self.continue_button.clicked.disconnect()
            if status == ExportStatus.ERROR_PRINTER_NOT_FOUND:
                self.continue_button.clicked.connect(self._show_insert_usb_message)
            else:
                self.continue_button.clicked.connect(self._show_error_message)

            self.continue_button.setEnabled(True)
            self.continue_button.setFocus()
        elif status == ExportStatus.ERROR_PRINTER_NOT_FOUND:
            self._show_insert_usb_message()
        else:
            self._show_error_message()
