"""
A dialog for journalists to print a conversation.

Copyright (C) 2018  The Freedom of the Press Foundation.

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published
by the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
"""
from gettext import gettext as _

from PyQt5.QtCore import QSize, pyqtSlot

from securedrop_client.export import ExportError, ExportStatus
from securedrop_client.gui import SecureQLabel
from securedrop_client.gui.dialogs import ModalDialog  # should eventually come from gui
from securedrop_client.logic import Controller


class PrintDialog(ModalDialog):

    FILENAME_WIDTH_PX = 260

    def __init__(self, controller: Controller, file_uuid: str, file_name: str) -> None:
        super().__init__()

        self.controller = controller
        self.file_uuid = file_uuid
        self.file_name = SecureQLabel(
            file_name, wordwrap=False, max_length=self.FILENAME_WIDTH_PX
        ).text()
        self.error_status = ""  # Hold onto the error status we receive from the Export VM

        # Connect controller signals to slots
        self.controller.export.printer_preflight_success.connect(self._on_preflight_success)
        self.controller.export.printer_preflight_failure.connect(self._on_preflight_failure)

        # Connect parent signals to slots
        self.continue_button.setEnabled(False)
        self.continue_button.clicked.connect(self._run_preflight)

        # Dialog content
        self.starting_header = _(
            "Preparing to print:"
            "<br />"
            '<span style="font-weight:normal">{}</span>'.format(self.file_name)
        )
        self.ready_header = _(
            "Ready to print:"
            "<br />"
            '<span style="font-weight:normal">{}</span>'.format(self.file_name)
        )
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
    def _run_preflight(self) -> None:
        self.controller.run_printer_preflight_checks()

    @pyqtSlot()
    def _print_file(self) -> None:
        self.controller.print_file(self.file_uuid)
        self.close()

    @pyqtSlot()
    def _on_preflight_success(self) -> None:
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
    def _on_preflight_failure(self, error: ExportError) -> None:
        self.stop_animate_header()
        self.header_icon.update_image("printer.svg", svg_size=QSize(64, 64))
        self.error_status = error.status
        # If the continue button is disabled then this is the result of a background preflight check
        if not self.continue_button.isEnabled():
            self.continue_button.clicked.disconnect()
            if error.status == ExportStatus.PRINTER_NOT_FOUND.value:
                self.continue_button.clicked.connect(self._show_insert_usb_message)
            else:
                self.continue_button.clicked.connect(self._show_generic_error_message)

            self.continue_button.setEnabled(True)
            self.continue_button.setFocus()
        else:
            if error.status == ExportStatus.PRINTER_NOT_FOUND.value:
                self._show_insert_usb_message()
            else:
                self._show_generic_error_message()
