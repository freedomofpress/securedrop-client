"""
A dialog that allows journalists to export sensitive files to a USB drive.
"""
from gettext import gettext as _
from typing import Optional

from pkg_resources import resource_string
from PyQt5.QtCore import QSize, Qt, pyqtSlot
from PyQt5.QtGui import QColor, QFont
from PyQt5.QtWidgets import QGraphicsDropShadowEffect, QLineEdit, QVBoxLayout, QWidget

from securedrop_client.export import ExportError, ExportStatus
from securedrop_client.gui.base import ModalDialog, PasswordEdit, SecureQLabel
from securedrop_client.gui.base.checkbox import SDCheckBox

from .device import Device


class FileDialog(ModalDialog):

    DIALOG_CSS = resource_string(__name__, "dialog.css").decode("utf-8")

    PASSPHRASE_LABEL_SPACING = 0.5
    NO_MARGIN = 0
    FILENAME_WIDTH_PX = 260

    def __init__(self, device: Device, file_uuid: str, file_name: str) -> None:
        super().__init__()
        self.setStyleSheet(self.DIALOG_CSS)

        self._device = device
        self.file_uuid = file_uuid
        self.file_name = SecureQLabel(
            file_name, wordwrap=False, max_length=self.FILENAME_WIDTH_PX
        ).text()
        # Hold onto the error status we receive from the Export VM
        self.error_status: Optional[ExportStatus] = None

        # Connect device signals to slots
        self._device.export_preflight_check_succeeded.connect(
            self._on_export_preflight_check_succeeded
        )
        self._device.export_preflight_check_failed.connect(self._on_export_preflight_check_failed)
        self._device.export_succeeded.connect(self._on_export_succeeded)
        self._device.export_failed.connect(self._on_export_failed)

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
        self.insert_usb_header = _("Insert encrypted USB drive")
        self.passphrase_header = _("Enter passphrase for USB drive")
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
        self.exporting_message = _("Exporting: {}").format(self.file_name)
        self.insert_usb_message = _(
            "Please insert one of the export drives provisioned specifically "
            "for the SecureDrop Workstation."
        )
        self.usb_error_message = _(
            "Either the drive is not encrypted or there is something else wrong with it."
        )
        self.passphrase_error_message = _("The passphrase provided did not work. Please try again.")
        self.generic_error_message = _("See your administrator for help.")
        self.success_message = _(
            "Remember to be careful when working with files outside of your Workstation machine."
        )

        # Passphrase Form
        self.passphrase_form = QWidget()
        self.passphrase_form.setObjectName("FileDialog_passphrase_form")
        passphrase_form_layout = QVBoxLayout()
        passphrase_form_layout.setContentsMargins(
            self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN
        )
        self.passphrase_form.setLayout(passphrase_form_layout)
        passphrase_label = SecureQLabel(_("Passphrase"))
        font = QFont()
        font.setLetterSpacing(QFont.AbsoluteSpacing, self.PASSPHRASE_LABEL_SPACING)
        passphrase_label.setFont(font)
        self.passphrase_field = PasswordEdit(self)
        self.passphrase_field.setEchoMode(QLineEdit.Password)
        effect = QGraphicsDropShadowEffect(self)
        effect.setOffset(0, -1)
        effect.setBlurRadius(4)
        effect.setColor(QColor("#aaa"))
        self.passphrase_field.setGraphicsEffect(effect)

        check = SDCheckBox()
        check.checkbox.stateChanged.connect(self.passphrase_field.on_toggle_password_Action)

        passphrase_form_layout.addWidget(passphrase_label)
        passphrase_form_layout.addWidget(self.passphrase_field)
        passphrase_form_layout.addWidget(check, alignment=Qt.AlignRight)
        self.body_layout.addWidget(self.passphrase_form)
        self.passphrase_form.hide()

        self._show_starting_instructions()
        self.start_animate_header()
        self._run_preflight()

    def _show_starting_instructions(self) -> None:
        self.header.setText(self.starting_header)
        self.body.setText(self.starting_message)
        self.adjustSize()

    def _show_passphrase_request_message(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self._export_file)
        self.header.setText(self.passphrase_header)
        self.continue_button.setText(_("SUBMIT"))
        self.header_line.hide()
        self.error_details.hide()
        self.body.hide()
        self.passphrase_field.setFocus()
        self.passphrase_form.show()
        self.adjustSize()

    def _show_passphrase_request_message_again(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self._export_file)
        self.header.setText(self.passphrase_header)
        self.error_details.setText(self.passphrase_error_message)
        self.continue_button.setText(_("SUBMIT"))
        self.header_line.hide()
        self.body.hide()
        self.error_details.show()
        self.passphrase_field.setFocus()
        self.passphrase_form.show()
        self.adjustSize()

    def _show_success_message(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self.close)
        self.header.setText(self.success_header)
        self.continue_button.setText(_("DONE"))
        self.body.setText(self.success_message)
        self.cancel_button.hide()
        self.error_details.hide()
        self.passphrase_form.hide()
        self.header_line.show()
        self.body.show()
        self.adjustSize()

    def _show_insert_usb_message(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self._run_preflight)
        self.header.setText(self.insert_usb_header)
        self.continue_button.setText(_("CONTINUE"))
        self.body.setText(self.insert_usb_message)
        self.error_details.hide()
        self.passphrase_form.hide()
        self.header_line.show()
        self.body.show()
        self.adjustSize()

    def _show_insert_encrypted_usb_message(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self._run_preflight)
        self.header.setText(self.insert_usb_header)
        self.error_details.setText(self.usb_error_message)
        self.continue_button.setText(_("CONTINUE"))
        self.body.setText(self.insert_usb_message)
        self.passphrase_form.hide()
        self.header_line.show()
        self.error_details.show()
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
        self.passphrase_form.hide()
        self.header_line.show()
        self.body.show()
        self.adjustSize()

    @pyqtSlot()
    def _run_preflight(self) -> None:
        self._device.run_export_preflight_checks()

    @pyqtSlot()
    def _export_file(self, checked: bool = False) -> None:
        self.start_animate_activestate()
        self.cancel_button.setEnabled(False)
        self.passphrase_field.setDisabled(True)
        self._device.export_file_to_usb_drive(self.file_uuid, self.passphrase_field.text())

    @pyqtSlot()
    def _on_export_preflight_check_succeeded(self) -> None:
        # If the continue button is disabled then this is the result of a background preflight check
        self.stop_animate_header()
        self.header_icon.update_image("savetodisk.svg", QSize(64, 64))
        self.header.setText(self.ready_header)
        if not self.continue_button.isEnabled():
            self.continue_button.clicked.disconnect()
            self.continue_button.clicked.connect(self._show_passphrase_request_message)
            self.continue_button.setEnabled(True)
            self.continue_button.setFocus()
            return

        self._show_passphrase_request_message()

    @pyqtSlot(object)
    def _on_export_preflight_check_failed(self, error: ExportError) -> None:
        self.stop_animate_header()
        self.header_icon.update_image("savetodisk.svg", QSize(64, 64))
        self._update_dialog(error.status)

    @pyqtSlot()
    def _on_export_succeeded(self) -> None:
        self.stop_animate_activestate()
        self._show_success_message()

    @pyqtSlot(object)
    def _on_export_failed(self, error: ExportError) -> None:
        self.stop_animate_activestate()
        self.cancel_button.setEnabled(True)
        self.passphrase_field.setDisabled(False)
        self._update_dialog(error.status)

    def _update_dialog(self, error_status: ExportStatus) -> None:
        self.error_status = error_status
        # If the continue button is disabled then this is the result of a background preflight check
        if not self.continue_button.isEnabled():
            self.continue_button.clicked.disconnect()
            if self.error_status == ExportStatus.BAD_PASSPHRASE:
                self.continue_button.clicked.connect(self._show_passphrase_request_message_again)
            elif self.error_status == ExportStatus.USB_NOT_CONNECTED:
                self.continue_button.clicked.connect(self._show_insert_usb_message)
            elif self.error_status == ExportStatus.DISK_ENCRYPTION_NOT_SUPPORTED_ERROR:
                self.continue_button.clicked.connect(self._show_insert_encrypted_usb_message)
            else:
                self.continue_button.clicked.connect(self._show_generic_error_message)

            self.continue_button.setEnabled(True)
            self.continue_button.setFocus()
        else:
            if self.error_status == ExportStatus.BAD_PASSPHRASE:
                self._show_passphrase_request_message_again()
            elif self.error_status == ExportStatus.USB_NOT_CONNECTED:
                self._show_insert_usb_message()
            elif self.error_status == ExportStatus.DISK_ENCRYPTION_NOT_SUPPORTED_ERROR:
                self._show_insert_encrypted_usb_message()
            else:
                self._show_generic_error_message()
