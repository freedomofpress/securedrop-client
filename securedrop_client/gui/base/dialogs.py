"""
A SecureDrop-themed modal dialog.

Copyright (C) 2021  The Freedom of the Press Foundation.

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published
by the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
"""
from gettext import gettext as _

from pkg_resources import resource_string
from PyQt5.QtCore import QSize, Qt
from PyQt5.QtGui import QIcon, QKeyEvent, QPixmap
from PyQt5.QtWidgets import (
    QApplication,
    QDialog,
    QDialogButtonBox,
    QHBoxLayout,
    QLabel,
    QPushButton,
    QVBoxLayout,
    QWidget,
)

from securedrop_client.gui.base.misc import SvgLabel
from securedrop_client.resources import load_movie


class ModalDialog(QDialog):

    DIALOG_CSS = resource_string(__name__, "dialogs.css").decode("utf-8")
    BUTTON_CSS = resource_string(__name__, "dialog_button.css").decode("utf-8")
    ERROR_DETAILS_CSS = resource_string(__name__, "dialog_message.css").decode("utf-8")

    MARGIN = 40
    NO_MARGIN = 0

    def __init__(self, show_header: bool = True, dangerous: bool = False) -> None:
        parent = QApplication.activeWindow()
        super().__init__(parent)
        self.setObjectName("ModalDialog")
        self.setStyleSheet(self.DIALOG_CSS)
        self.setModal(True)

        self.show_header = show_header
        self.dangerous = dangerous
        if self.dangerous:
            self.setProperty("class", "dangerous")

        # Widget for displaying error messages
        self.error_details = QLabel()
        self.error_details.setObjectName("ModalDialog_error_details")
        self.error_details.setStyleSheet(self.ERROR_DETAILS_CSS)
        self.error_details.setWordWrap(True)
        self.error_details.hide()

        # Body to display instructions and forms
        self.body = QLabel()
        self.body.setObjectName("ModalDialog_body")
        self.body.setWordWrap(True)
        self.body.setScaledContents(True)
        body_container = QWidget()
        self.body_layout = QVBoxLayout()
        self.body_layout.setContentsMargins(
            self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN
        )
        body_container.setLayout(self.body_layout)
        self.body_layout.addWidget(self.body)

        # Main widget layout
        layout = QVBoxLayout(self)
        layout.setContentsMargins(self.MARGIN, self.MARGIN, self.MARGIN, self.MARGIN)
        self.setLayout(layout)

        if self.show_header:
            # Header for icon and task title
            header_container = QWidget()
            header_container_layout = QHBoxLayout()
            header_container.setLayout(header_container_layout)
            self.header_icon = SvgLabel("blank.svg", svg_size=QSize(64, 64))
            self.header_icon.setObjectName("ModalDialog_header_icon")
            self.header_spinner = QPixmap()
            self.header_spinner_label = QLabel()
            self.header_spinner_label.setObjectName("ModalDialog_header_spinner")
            self.header_spinner_label.setMinimumSize(64, 64)
            self.header_spinner_label.setVisible(False)
            self.header_spinner_label.setPixmap(self.header_spinner)
            self.header = QLabel()
            self.header.setObjectName("ModalDialog_header")
            header_container_layout.addWidget(self.header_icon)
            header_container_layout.addWidget(self.header_spinner_label)
            header_container_layout.addWidget(self.header, alignment=Qt.AlignCenter)
            header_container_layout.addStretch()

            self.header_line = QWidget()
            self.header_line.setObjectName("ModalDialog_header_line")

            layout.addWidget(header_container)
            layout.addWidget(self.header_line)

        layout.addWidget(self.error_details)
        layout.addWidget(body_container)
        layout.addWidget(self.configure_buttons())

        # Activestate animation.
        self.button_animation = load_movie("activestate-wide.gif")
        self.button_animation.setScaledSize(QSize(32, 32))
        self.button_animation.frameChanged.connect(self.animate_activestate)

        # Header animation.
        self.header_animation = load_movie("header_animation.gif")
        self.header_animation.setScaledSize(QSize(64, 64))
        self.header_animation.frameChanged.connect(self.animate_header)

    def configure_buttons(self) -> QWidget:
        # Buttons to continue and cancel
        window_buttons = QWidget()
        window_buttons.setObjectName("ModalDialog_window_buttons")

        button_layout = QVBoxLayout()
        window_buttons.setLayout(button_layout)

        self.cancel_button = QPushButton(_("CANCEL"))
        self.cancel_button.setStyleSheet(self.BUTTON_CSS)

        self.continue_button = QPushButton(_("CONTINUE"))
        self.continue_button.setStyleSheet(self.BUTTON_CSS)
        self.continue_button.setIconSize(QSize(21, 21))

        button_box = QDialogButtonBox(Qt.Horizontal)
        button_box.setObjectName("ModalDialog_button_box")

        if self.dangerous:
            self.cancel_button.setAutoDefault(True)
            self.continue_button.setDefault(False)
            self.cancel_button.setObjectName("ModalDialog_primary_button")
            self.continue_button.setObjectName("ModalDialog_cancel_button")
        else:
            self.cancel_button.setAutoDefault(False)
            self.continue_button.setDefault(True)
            self.cancel_button.setObjectName("ModalDialog_cancel_button")
            self.continue_button.setObjectName("ModalDialog_primary_button")

        button_box.addButton(self.cancel_button, QDialogButtonBox.RejectRole)
        button_box.addButton(self.continue_button, QDialogButtonBox.AcceptRole)

        button_box.rejected.connect(self.reject)
        button_box.accepted.connect(self.accept)

        self.confirmation_label = QLabel()
        self.confirmation_label.setObjectName("ModalDialogConfirmation")
        button_layout.addWidget(self.confirmation_label, 0, Qt.AlignLeft | Qt.AlignBottom)

        button_layout.addWidget(button_box, alignment=Qt.AlignLeft)

        button_layout.setContentsMargins(
            self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN
        )

        return window_buttons

    def keyPressEvent(self, event: QKeyEvent) -> None:
        if event.key() == Qt.Key_Enter or event.key() == Qt.Key_Return:
            if self.cancel_button.hasFocus():
                self.cancel_button.click()
            else:
                self.continue_button.click()
        else:
            super().keyPressEvent(event)

    def animate_activestate(self) -> None:
        self.continue_button.setIcon(QIcon(self.button_animation.currentPixmap()))

    def animate_header(self) -> None:
        self.header_spinner_label.setPixmap(self.header_animation.currentPixmap())

    def start_animate_activestate(self) -> None:
        self.button_animation.start()
        self.continue_button.setText("")
        self.continue_button.setMinimumSize(QSize(142, 43))
        # Reset widget stylesheets
        self.continue_button.setStyleSheet("")
        self.continue_button.setObjectName("ModalDialog_primary_button_active")
        self.continue_button.setStyleSheet(self.BUTTON_CSS)
        self.error_details.setStyleSheet("")
        self.error_details.setObjectName("ModalDialog_error_details_active")
        self.error_details.setStyleSheet(self.ERROR_DETAILS_CSS)

    def start_animate_header(self) -> None:
        self.header_icon.setVisible(False)
        self.header_spinner_label.setVisible(True)
        self.header_animation.start()

    def stop_animate_activestate(self) -> None:
        self.continue_button.setIcon(QIcon())
        self.button_animation.stop()
        self.continue_button.setText(_("CONTINUE"))
        # Reset widget stylesheets
        self.continue_button.setStyleSheet("")
        self.continue_button.setObjectName("ModalDialog_primary_button")
        self.continue_button.setStyleSheet(self.BUTTON_CSS)
        self.error_details.setStyleSheet("")
        self.error_details.setObjectName("ModalDialog_error_details")
        self.error_details.setStyleSheet(self.ERROR_DETAILS_CSS)

    def stop_animate_header(self) -> None:
        self.header_icon.setVisible(True)
        self.header_spinner_label.setVisible(False)
        self.header_animation.stop()

    def text(self) -> str:
        """A text-only representation of the dialog."""
        return self.body.text()
