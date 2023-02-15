from gettext import gettext as _
from typing import List

from PyQt5.QtCore import pyqtSlot

from .device import Device
from .file_dialog import FileDialog


class ExportDialog(ModalDialog):
    DIALOG_CSS = resource_string(__name__, "dialog.css").decode("utf-8")

    def __init__(self, device: Device, summary: str, file_locations: List[str]) -> None:
        super().__init__(device, "", summary)

        self.file_locations = file_locations

    @pyqtSlot(bool)
    def _export_files(self, checked: bool = False) -> None:
        self.start_animate_activestate()
        self.cancel_button.setEnabled(False)
        self.passphrase_field.setDisabled(True)
        self._device.export_files(self.file_locations, self.passphrase_field.text())

    @pyqtSlot()
    def _show_passphrase_request_message(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self._export_files)
        self.header.setText(self.passphrase_header)
        self.continue_button.setText(_("SUBMIT"))
        self.header_line.hide()
        self.error_details.hide()
        self.body.hide()
        self.passphrase_field.setFocus()
        self.passphrase_form.show()
        self.adjustSize()

    @pyqtSlot()
    def _show_passphrase_request_message_again(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self._export_files)
        self.header.setText(self.passphrase_header)
        self.error_details.setText(self.passphrase_error_message)
        self.continue_button.setText(_("SUBMIT"))
        self.header_line.hide()
        self.body.hide()
        self.error_details.show()
        self.passphrase_field.setFocus()
        self.passphrase_form.show()
        self.adjustSize()
