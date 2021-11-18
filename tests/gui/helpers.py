from PyQt5.QtCore import Qt
from PyQt5.QtTest import QTest
from PyQt5.QtWidgets import QWidget


def press_alt_key(receiver: QWidget) -> None:
    """Emit a KeyPressEvent with an 'Alt' key."""
    # I couln't find a way to send "Alt" without sending another key as well.
    QTest.keyClicks(receiver, " ", Qt.AltModifier)
