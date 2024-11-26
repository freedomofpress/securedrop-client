import math
import time

from PyQt5.QtCore import QTimer, pyqtSignal
from PyQt5.QtWidgets import QProgressBar

from securedrop_client.sdk import ProgressProxy
from securedrop_client.utils import humanize_speed

SMOOTHING_FACTOR = 0.3


class FileDownloadProgressBar(QProgressBar):
    """
    A progress bar for file downloads.

    It receives progress updates from the SDK and updates the total % downloaded,
    as well as calculating the current speed.

    We use an exponential moving average to smooth out the speed as suggested by
    https://stackoverflow.com/a/3841706; the reported speed is 30% of the current
    speed and 70% of the previous speed. It is updated every 100ms.
    """

    signal = pyqtSignal(int)

    def __init__(self, file_size: int) -> None:
        super().__init__()
        self.setObjectName("FileDownloadProgressBar")
        self.setMaximum(file_size)
        # n.b. we only update the bar's value and let the text get updated by
        # the timer in update_speed
        self.signal.connect(self.setValue)
        self.timer = QTimer(self)
        self.timer.setInterval(100)
        self.timer.timeout.connect(self.update_speed)
        self.timer.start()
        # The most recently calculated speed
        self.speed = 0.0
        # The last time we updated the speed
        self.last_total_time = 0.0
        # The number of bytes downloaded the last time we updated the speed
        self.last_total_bytes = 0

    def update_display(self) -> None:
        """Update the text displayed in the progress bar."""
        # Use math.floor so we don't show 100% until we're actually done
        percentage = math.floor((self.value() / self.maximum()) * 100)
        formatted_speed = humanize_speed(self.speed)
        # TODO: localize this?
        if percentage in (0, 100):
            # If haven't started or have finished, don't display a 0B/s speed
            self.setFormat(f"{percentage}%")
        else:
            self.setFormat(f"{percentage}% | {formatted_speed}")

    def update_speed(self) -> None:
        """Calculate the new speed and trigger updating the display."""
        now = time.monotonic()
        value = self.value()

        # If this is the first update we report the speed as 0
        if self.last_total_time == 0:
            self.last_total_time = now
            self.last_total_bytes = value
            self.speed = 0
            return

        time_diff = now - self.last_total_time
        bytes_diff = value - self.last_total_bytes
        if time_diff > 0:
            self.speed = (
                1 - SMOOTHING_FACTOR
            ) * self.speed + SMOOTHING_FACTOR * bytes_diff / time_diff

        self.last_total_time = now
        self.last_total_bytes = value
        self.update_display()

    def proxy(self) -> ProgressProxy:
        """Get a proxy that updates this widget."""
        return ProgressProxy(self.signal)
