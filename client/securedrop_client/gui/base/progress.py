from PyQt5.QtCore import pyqtSignal
from PyQt5.QtWidgets import QProgressBar

from securedrop_client.utils import humanize_filesize


class FileDownloadProgressBar(QProgressBar):
    """
    A progress bar for file downloads.

    Use the signal to increment the progress; see the SDK's ProgressProxy type.
    """

    # first value is bytes fetched, second is smoothed speed in bytes/second
    signal = pyqtSignal((int, int))

    def __init__(self, file_size: int) -> None:
        super().__init__()
        self.setObjectName("FileDownloadProgressBar")
        self.setMaximum(file_size)
        self.signal.connect(self.update_progress)

    def update_progress(self, fetched: int, speed: int) -> None:
        self.setValue(fetched)
        percentage = int((fetched / self.maximum()) * 100)
        # TODO: does this remove too much precision?
        formatted_speed = humanize_filesize(speed) + "/s"
        # TODO: localize this?
        self.setFormat(f"{percentage}% | {formatted_speed}")
