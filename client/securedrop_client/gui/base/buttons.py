"""
SecureDrop Buttons

These buttons are styled for the SecureDrop Client. If you feel like a button
requires special styling, adding it here is likely a good call.

All buttons in this file must inherit from QAbstractButton,
so that they implement the accessibility features provided by Qt.

Please be as specific as possible when inheriting from Qt buttons.
For example, SDPushButton inherits from QPushButton in order to
take advantage of as many Qt-maintained features as possible.

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

from typing import NewType, Optional

from PyQt5.QtWidgets import QPushButton, QWidget

from securedrop_client.resources import load_css


class SDPushButton(QPushButton):
    """A QPushButton that follows SecureDrop guidelines."""

    Alignment = NewType("Alignment", str)
    AlignLeft = Alignment("left-aligned")

    def __init__(self, parent: Optional[QWidget] = None) -> None:
        super().__init__(parent)
        self.setStyleSheet(load_css("button.css"))

    def setAlignment(self, align: Alignment) -> None:
        """Visually align a button that doesn't have a visible outline."""
        self.setProperty("class", f"button text {align}")
