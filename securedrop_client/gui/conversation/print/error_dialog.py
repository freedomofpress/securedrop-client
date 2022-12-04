from gettext import gettext as _

from PyQt5.QtCore import QSize

from securedrop_client.gui.base import ModalDialog, SecureQLabel


class ErrorDialog(ModalDialog):

    FILENAME_WIDTH_PX = 260

    def __init__(self, file_name: str, reason: str) -> None:
        super().__init__()

        self.continue_button.clicked.connect(
            self.accept
        )  # FIXME The ModalDialog is more complex than needed to do this.

        file_name = SecureQLabel(
            file_name, wordwrap=False, max_length=self.FILENAME_WIDTH_PX
        ).text()  # FIXME This seems like a heavy way to sanitize a string.
        reason = SecureQLabel(
            reason, wordwrap=False, max_length=self.FILENAME_WIDTH_PX
        ).text()  # FIXME This seems like a heavy way to sanitize a string.
        header = _("Printing failed<br />" '<span style="font-weight:normal">{}</span>').format(
            file_name
        )

        self.header.setText(header)
        self.header_icon.update_image("printer.svg", svg_size=QSize(64, 64))
        self.body.setText(reason)
        self.adjustSize()
