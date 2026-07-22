import math
import time

from PyQt5.QtCore import QTimer, pyqtBoundSignal, pyqtSignal
from PyQt5.QtWidgets import QProgressBar

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

    size_signal = pyqtSignal(int)
    decrypting_signal = pyqtSignal(bool)

    def __init__(self, file_size: int) -> None:
        super().__init__()
        self.setObjectName("FileDownloadProgressBar")
        self.setMaximum(file_size)
        # n.b. we only update the bar's value and let the text get updated by
        # the timer in update_speed
        self.size_signal.connect(self.setValue)
        self.decrypting_signal.connect(self.handle_decrypting)
        self.speed_timer = QTimer(self)
        self.speed_timer.setInterval(100)
        self.speed_timer.timeout.connect(self.update_speed)
        self.speed_timer.start()
        self.display_timer = QTimer(self)
        self.display_timer.setInterval(1000)
        self.display_timer.timeout.connect(self.update_display)
        self.display_timer.start()
        # The most recently calculated speed
        self.speed = 0.0
        # The last time we updated the speed
        self.last_total_time = 0.0
        # The number of bytes downloaded the last time we updated the speed
        self.last_total_bytes = 0

    def handle_decrypting(self, decrypting: bool) -> None:
        if decrypting:
            # Stop the timers and then switch to an indeterminate progress bar
            self.speed_timer.stop()
            self.display_timer.stop()
            self.setMaximum(0)
            self.setValue(0)

    def update_display(self) -> None:
        """Update the text displayed in the progress bar."""
        # Use math.floor so we don't show 100% until we're actually done
        maximum = self.maximum()
        if maximum == 0:
            # Race condition: we've likely switched to the indeterminate progress bar
            # which has a maximum of 0. Treat it like 100% even though it won't show up
            # just to avoid the DivisionByZero error.
            percentage = 100
        else:
            # Calculate the raw percentage, round down to the nearest integer, but make sure it's
            # not a negative number.
            percentage = max(math.floor((self.value() / maximum) * 100), 0)
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

    def proxy(self) -> "ProgressProxy":
        """Get a proxy that updates this widget."""
        return ProgressProxy(self.size_signal, self.decrypting_signal)


class ProgressProxy:
    """
    Relay the current download progress over to the UI; see
    the FileDownloadProgressBar widget.
    """

    def __init__(self, size_signal: pyqtBoundSignal, decrypting_signal: pyqtBoundSignal) -> None:
        self.size_signal = size_signal
        self.decrypting_signal = decrypting_signal

    def set_value(self, value: int) -> None:
        self.size_signal.emit(value)

    def set_decrypting(self) -> None:
        self.decrypting_signal.emit(True)
