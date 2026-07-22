from enum import Enum

from PyQt5.QtCore import Qt


class Shortcuts(Enum):
    """Central listing of all keyboard shortcuts"""

    DOWNLOAD_CONVERSATION = Qt.CTRL + Qt.Key_D
    QUIT = Qt.CTRL + Qt.Key_Q  # Same as QKeySequence.Quit
    SEND = Qt.CTRL + Qt.Key_Return
