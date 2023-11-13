"""
SecureDrop customized passphrase checkbox control

A checkbox control created to toggle with hiding and showing PasswordEdit passphrases.
Consists of a QCheckBox and a QLabel positioned horizontally within a QFrame.
Present in the Sign-in and Export Dialog.
"""

from gettext import gettext as _

from PyQt5.QtCore import Qt, pyqtSignal
from PyQt5.QtGui import QCursor, QFont, QMouseEvent
from PyQt5.QtWidgets import QCheckBox, QFrame, QHBoxLayout, QLabel, QWidget

from securedrop_client.resources import load_relative_css


class SDCheckBox(QWidget):
    clicked = pyqtSignal()
    PASSPHRASE_LABEL_SPACING = 1

    def __init__(self) -> None:
        super().__init__()
        self.setObjectName("ShowPassphrase_widget")
        self.setStyleSheet(load_relative_css(__file__, "checkbox.css"))

        font = QFont()
        font.setLetterSpacing(QFont.AbsoluteSpacing, self.PASSPHRASE_LABEL_SPACING)

        self._layout = QHBoxLayout()
        self._layout.setContentsMargins(0, 0, 0, 0)
        self._layout.setSpacing(0)
        self.setLayout(self._layout)

        self.frame = QFrame()
        self.frame.setLayout(QHBoxLayout())
        self.frame.layout().setContentsMargins(0, 0, 0, 0)
        self.frame.layout().setSpacing(0)

        self.checkbox = QCheckBox()
        self.label = QLabel(_("Show Passphrase"))
        self.label.setFont(font)

        self._layout.addWidget(self.frame)
        self.frame.layout().addWidget(self.checkbox)
        self.frame.layout().addWidget(self.label)
        self.frame.setCursor(QCursor(Qt.PointingHandCursor))

        self.clicked.connect(self.checkbox.click)

    def mousePressEvent(self, e: QMouseEvent) -> None:
        self.clicked.emit()
