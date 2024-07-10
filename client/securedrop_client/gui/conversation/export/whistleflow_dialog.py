"""
A dialog that allows journalists to export conversations or transcripts to the
Whistleflow View VM. This is a clone of FileDialog.
"""
import datetime
import logging
from gettext import gettext as _
from typing import List, Optional

from pkg_resources import resource_string
from PyQt5.QtCore import QSize, pyqtSlot

from securedrop_client.export import ExportError, ExportStatus
from securedrop_client.gui.base import ModalDialog, SecureQLabel

from .device import Device

logger = logging.getLogger(__name__)


class WhistleflowDialog(ModalDialog):
    DIALOG_CSS = resource_string(__name__, "dialog.css").decode("utf-8")

    PASSPHRASE_LABEL_SPACING = 0.5
    NO_MARGIN = 0
    FILENAME_WIDTH_PX = 260

    def __init__(self, device: Device, summary: str, file_locations: List[str]) -> None:
        super().__init__()
        self.setStyleSheet(self.DIALOG_CSS)

        self._device = device
        self._file_locations = file_locations
        self.file_name = SecureQLabel(
            summary, wordwrap=False, max_length=self.FILENAME_WIDTH_PX
        ).text()
        # Hold onto the error status we receive from the Export VM
        self.error_status: Optional[ExportStatus] = None

        # Connect device signals to slots
        self._device.whistleflow_export_preflight_check_succeeded.connect(
            self._on_export_preflight_check_succeeded
        )
        self._device.whistleflow_export_preflight_check_failed.connect(
            self._on_export_preflight_check_failed
        )
        self._device.export_completed.connect(self._on_export_succeeded)
        self._device.whistleflow_export_failed.connect(self._on_export_failed)
        self._device.whistleflow_export_succeeded.connect(self._on_export_succeeded)

        # Connect parent signals to slots
        self.continue_button.setEnabled(False)
        self.continue_button.clicked.connect(self._run_preflight)

        # Dialog content
        self.starting_header = _(
            "Preparing to export:<br />" '<span style="font-weight:normal">{}</span>'
        ).format(self.file_name)
        self.ready_header = _(
            "Ready to export:<br />" '<span style="font-weight:normal">{}</span>'
        ).format(self.file_name)
        self.success_header = _("Export successful")
        self.error_header = _("Export failed")
        self.starting_message = _(
            "<h2>Understand the risks before exporting files</h2>"
            "<b>Malware</b>"
            "<br />"
            "This workstation lets you open files securely. If you open files on another "
            "computer, any embedded malware may spread to your computer or network. If you are "
            "unsure how to manage this risk, please print the file, or contact your "
            "administrator."
            "<br /><br />"
            "<b>Anonymity</b>"
            "<br />"
            "Files submitted by sources may contain information or hidden metadata that "
            "identifies who they are. To protect your sources, please consider redacting files "
            "before working with them on network-connected computers."
        )
        self.generic_error_message = _("See your administrator for help.")
        self.success_message = _(
            "Remember to be careful when working with files outside of your Workstation machine."
        )

        self._show_starting_instructions()
        self.start_animate_header()
        self._run_preflight()

    def _show_starting_instructions(self) -> None:
        self.header.setText(self.starting_header)
        self.body.setText(self.starting_message)
        self.adjustSize()

    def _send_to_whistleflow(self) -> None:
        timestamp = datetime.datetime.now().isoformat()
        self._device.whistleflow_export_requested.emit(
            "export-{}.tar".format(timestamp), self._file_locations
        )

    def _show_success_message(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self.close)
        self.header.setText(self.success_header)
        self.continue_button.setText(_("DONE"))
        self.body.setText(self.success_message)
        self.cancel_button.hide()
        self.error_details.hide()
        self.header_line.show()
        self.body.show()
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
        self.header_line.show()
        self.body.show()
        self.adjustSize()

    @pyqtSlot()
    def _run_preflight(self) -> None:
        self._device.run_whistleflow_preflight_checks()

    @pyqtSlot()
    def _export_file(self, checked: bool = False) -> None:
        self.start_animate_activestate()
        self.cancel_button.setEnabled(False)
        self._device.export_files_to_whistleflow(self.file_name, self._file_locations)

    @pyqtSlot()
    def _on_export_preflight_check_succeeded(self) -> None:
        # If the continue button is disabled then this is the result of a background preflight check
        self.stop_animate_header()
        self.header_icon.update_image("savetodisk.svg", QSize(64, 64))
        self.header.setText(self.ready_header)
        if not self.continue_button.isEnabled():
            self.continue_button.clicked.disconnect()
            self.continue_button.clicked.connect(self._send_to_whistleflow)
            self.continue_button.setEnabled(True)
            self.continue_button.setFocus()
            return

        self._send_to_whistleflow()

    @pyqtSlot(object)
    def _on_export_preflight_check_failed(self, error: ExportError) -> None:
        self.stop_animate_header()
        self.header_icon.update_image("savetodisk.svg", QSize(64, 64))

    @pyqtSlot()
    def _on_export_succeeded(self) -> None:
        self.stop_animate_activestate()
        self._show_success_message()

    @pyqtSlot(object)
    def _on_export_failed(self, error: ExportError) -> None:
        self.stop_animate_activestate()
        self.cancel_button.setEnabled(True)
        logger.error(error.status)
