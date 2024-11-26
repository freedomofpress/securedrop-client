import time

from PyQt5.QtCore import pyqtBoundSignal

SMOOTHING_FACTOR = 0.3


class ProgressProxy:
    """
    Relay the current download progress over to the UI

    We smooth the speed over time to reduce noise by using
    an exponential moving average (motivated by https://stackoverflow.com/a/3841706).
    The reported speed is 30% of the current speed and 70% of the previous
    smoothed speed.
    """

    def __init__(self, inner: pyqtBoundSignal | None) -> None:
        self.inner = inner
        self.ema_speed = 0
        self.last_total_time: float | None = None
        self.last_total_bytes = 0

    def update_speed(self, value: int) -> None:
        now = time.time()

        # If this is the first update we report the speed as 0
        if self.last_total_time is None:
            self.last_total_time = value
            self.last_total_bytes = value
            self.ema_speed = 0
            return

        time_diff = now - self.last_total_time
        bytes_diff = value - self.last_total_bytes
        if time_diff > 0:
            self.ema_speed = int(
                (1 - SMOOTHING_FACTOR) * self.ema_speed + SMOOTHING_FACTOR * bytes_diff / time_diff
            )

        self.last_total_time = now
        self.last_total_bytes = value

    def set_value(self, value: int) -> None:
        if not self.inner:
            return

        self.update_speed(value)
        self.inner.emit(value, self.ema_speed)
