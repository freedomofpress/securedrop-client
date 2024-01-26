"""
A dialog that allows journalists to export sensitive files to a USB drive.
"""
from gettext import gettext as _
from typing import List

from PyQt5.QtCore import pyqtSlot

from .device import Device
from .file_dialog import FileDialog


class TranscriptDialog(FileDialog):
    """Adapts the dialog used to export files to allow exporting a conversation transcript.

    - Adjust the init arguments to the needs of conversation transcript export.
    - Adds a method to allow a transcript to be exported.
    - Overrides the two slots that handles the export action to call said method.
    """

    def __init__(self, device: Device, file_name: str, filepath: List[str]) -> None:
        super().__init__(device, file_name, filepath)

        # List[str] to foreshadow multifile export and combining all export dialogs
        self.transcript_location = filepath

    def _export_transcript(self, checked: bool = False) -> None:
        self.start_animate_activestate()
        self.cancel_button.setEnabled(False)
        self.passphrase_field.setDisabled(True)
        self._device.export(self.transcript_location, self.passphrase_field.text())

    @pyqtSlot()
    def _show_passphrase_request_message(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self._export_transcript)
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
        self.continue_button.clicked.connect(self._export_transcript)
        self.header.setText(self.passphrase_header)
        self.error_details.setText(self.passphrase_error_message)
        self.continue_button.setText(_("SUBMIT"))
        self.header_line.hide()
        self.body.hide()
        self.error_details.show()
        self.passphrase_field.setFocus()
        self.passphrase_form.show()
        self.adjustSize()
