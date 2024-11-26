from PyQt5.QtWidgets import QProgressBar


class Progress:
    def __init__(self, inner: QProgressBar | None) -> None:
        self.inner = inner

    def set_value(self, value: int) -> None:
        if self.inner:
            self.inner.setValue(value)
