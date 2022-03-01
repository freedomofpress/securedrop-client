"""
SecureDrop customized passphrase checkbox control

A checkbox control created to toggle with hiding and showing PasswordEdit passphrases.
Consists of a QCheckBox and a QLabel positioned horizontally within a QFrame.
Present in the Sign-in and Export Dialog.
"""
from pkg_resources import resource_string
from PyQt5.QtCore import Qt, pyqtSignal
from PyQt5.QtGui import QCursor, QFont, QMouseEvent
from PyQt5.QtWidgets import QCheckBox, QFrame, QHBoxLayout, QLabel, QWidget


class SDCheckBox(QWidget):
    clicked = pyqtSignal()
    CHECKBOX_CSS = resource_string(__name__, "checkbox.css").decode("utf-8")
    PASSPHRASE_LABEL_SPACING = 1

    def __init__(self) -> None:
        super().__init__()
        self.setObjectName("ShowPassphrase_widget")
        self.setStyleSheet(self.CHECKBOX_CSS)

        font = QFont()
        font.setLetterSpacing(QFont.AbsoluteSpacing, self.PASSPHRASE_LABEL_SPACING)

        self.layout = QHBoxLayout()
        self.layout.setContentsMargins(0, 0, 0, 0)
        self.layout.setSpacing(0)
        self.setLayout(self.layout)

        self.frame = QFrame()
        self.frame.setLayout(QHBoxLayout())
        self.frame.layout().setContentsMargins(0, 0, 0, 0)
        self.frame.layout().setSpacing(0)

        self.checkbox = QCheckBox()
        self.label = QLabel("Show Passphrase")
        self.label.setFont(font)

        self.layout.addWidget(self.frame)
        self.frame.layout().addWidget(self.checkbox)
        self.frame.layout().addWidget(self.label)
        self.frame.setCursor(QCursor(Qt.PointingHandCursor))

        self.clicked.connect(self.checkbox.click)

    def mousePressEvent(self, e: QMouseEvent) -> None:
        self.clicked.emit()
