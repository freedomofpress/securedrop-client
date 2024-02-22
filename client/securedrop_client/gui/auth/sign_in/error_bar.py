"""
A widget that displays error messages.

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

from pkg_resources import resource_string
from PyQt5.QtCore import QSize
from PyQt5.QtWidgets import QHBoxLayout, QWidget

from securedrop_client.gui.base import SecureQLabel, SvgLabel


class LoginErrorBar(QWidget):
    """
    A bar widget for displaying messages about login errors to the user.
    """

    def __init__(self) -> None:
        super().__init__()

        self.setObjectName("LoginErrorBar")
        styles = resource_string(__name__, "error_bar.css").decode("utf-8")
        self.setStyleSheet(styles)

        # Set layout
        layout = QHBoxLayout(self)
        self.setLayout(layout)

        # Remove margins and spacing
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Set size policy
        retain_space = self.sizePolicy()
        retain_space.setRetainSizeWhenHidden(True)
        self.setSizePolicy(retain_space)

        # Error icon
        self.error_icon = SvgLabel("error_icon_white.svg", svg_size=QSize(18, 18))
        self.error_icon.setObjectName("LoginErrorBar_icon")
        self.error_icon.setFixedWidth(42)

        # Error status bar
        self.error_status_bar = SecureQLabel(wordwrap=False)
        self.error_status_bar.setObjectName("LoginErrorBar_status_bar")
        self.setFixedHeight(42)

        # Create space ths size of the error icon to keep the error message centered
        spacer1 = QWidget()
        spacer2 = QWidget()

        # Add widgets to layout
        layout.addWidget(spacer1)
        layout.addWidget(self.error_icon)
        layout.addWidget(self.error_status_bar)
        layout.addWidget(spacer2)

    def set_message(self, message: str) -> None:
        self.show()
        self.error_status_bar.setText(message)

    def clear_message(self) -> None:
        self.error_status_bar.setText("")
        self.hide()
