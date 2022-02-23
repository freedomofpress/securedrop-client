"""

"""
from PyQt5.QtCore import Qt
from PyQt5.QtGui import QCursor, QFont
from PyQt5.QtWidgets import QCheckBox, QFrame, QHBoxLayout, QLabel, QWidget

from securedrop_client.resources import load_css


class SDCheckBox(QWidget):

    CHECKBOX_CSS = "checkbox.css"
    PASSPHRASE_LABEL_SPACING = 1

    def __init__(self) -> None:
        super().__init__()
        self.setObjectName("ShowPassphrase_widget")
        self.setStyleSheet(load_css(self.CHECKBOX_CSS))

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
