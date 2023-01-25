from PyQt5.QtCore import QSize, pyqtSlot

from securedrop_client.gui.conversation.export import PrintDialog

from .device import Device


class PrintTranscriptDialog(PrintDialog):
    def __init__(self, device: Device, file_name: str, transcript_location: str) -> None:
        super().__init__(device, "", file_name)

        self.transcript_location = transcript_location

    @pyqtSlot()
    def _print_transcript(self) -> None:
        self._device.print_transcript(self.transcript_location)
        self.close()

    @pyqtSlot()
    def _on_print_preflight_check_succeeded(self) -> None:
        # If the continue button is disabled then this is the result of a background preflight check
        self.stop_animate_header()
        self.header_icon.update_image("printer.svg", svg_size=QSize(64, 64))
        self.header.setText(self.ready_header)
        if not self.continue_button.isEnabled():
            self.continue_button.clicked.disconnect()
            self.continue_button.clicked.connect(self._print_transcript)

            self.continue_button.setEnabled(True)
            self.continue_button.setFocus()
            return

        self._print_transcript()
