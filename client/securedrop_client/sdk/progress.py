from PyQt5.QtCore import pyqtBoundSignal


class ProgressProxy:
    """
    Relay the current download progress over to the UI; see
    the FileDownloadProgressBar widget.
    """

    def __init__(self, inner: pyqtBoundSignal | None) -> None:
        self.inner = inner

    def set_value(self, value: int) -> None:
        if self.inner:
            self.inner.emit({"size": value})

    def set_decypting(self) -> None:
        if self.inner:
            self.inner.emit({"decrypting": True})
