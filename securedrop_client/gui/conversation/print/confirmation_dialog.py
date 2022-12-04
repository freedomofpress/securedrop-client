from gettext import gettext as _

from PyQt5.QtCore import QSize, pyqtSlot

from securedrop_client.export import Printer
from securedrop_client.gui.base import ModalDialog, SecureQLabel


class ConfirmationDialog(ModalDialog):

    FILENAME_WIDTH_PX = 260

    def __init__(self, printer: Printer, file_name: str) -> None:
        super().__init__()

        self._printer = printer
        print("when creating the dialog", self._printer.status)
        self._printer.status_changed.connect(self._on_printer_status_changed)

        self.continue_button.setText("PRINT")
        self.continue_button.clicked.connect(
            self.accept
        )  # FIXME The ModalDialog is more complex than needed to do this.

        file_name = SecureQLabel(
            file_name, wordwrap=False, max_length=self.FILENAME_WIDTH_PX
        ).text()  # FIXME This seems like a heavy way to sanitize a string.
        header = _("Print:<br />" '<span style="font-weight:normal">{}</span>').format(file_name)
        body = _(
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

        self.header.setText(header)
        self.header_icon.update_image("printer.svg", svg_size=QSize(64, 64))
        self.body.setText(body)
        self.adjustSize()

        self._body = body

        self._on_printer_status_changed()

    @pyqtSlot()
    def _on_printer_status_changed(self) -> None:
        printer_status = self._printer.status
        if printer_status == Printer.StatusUnknown:
            print("printer status became unknown")
            self._on_printer_status_unknown()
        elif printer_status == Printer.StatusReady:
            print("printer status ready")
            self._on_printer_ready()
        elif printer_status == Printer.StatusUnreachable:
            print("printer status unreachable")
            self._on_printer_unreachable()

    def _on_printer_status_unknown(self) -> None:
        self.continue_button.setEnabled(False)

        status = "<i>Waiting for printer status to be known...</i>"
        self.body.setText("<br /><br />".join([self._body, status]))
        self.adjustSize()

    def _on_printer_ready(self) -> None:
        self.continue_button.setEnabled(True)

        self.body.setText(self._body)
        self.adjustSize()

    def _on_printer_unreachable(self) -> None:
        self.continue_button.setEnabled(False)

        status = "<i>Printer unreachable, please verify it's connected.</i>"
        self.body.setText("<br /><br />".join([self._body, status]))
        self.adjustSize()
