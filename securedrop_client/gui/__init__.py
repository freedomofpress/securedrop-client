"""
Generic custom widgets.

Copyright (C) 2018  The Freedom of the Press Foundation.

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
import textwrap

from typing import Union

from PyQt5.QtWidgets import QLabel, QHBoxLayout, QPushButton, QWidget
from PyQt5.QtCore import QSize, Qt

from securedrop_client.resources import load_svg, load_icon


class SvgToggleButton(QPushButton):
    """
    A toggle button used to display the contents of Scalable Vector Graphics (SVG) files provided
    for an on and off state.

    Parameters
    ----------
    on: str
        The name of the SVG file to add to the button for on state.
    off: str
        The name of the SVG file to add to the button for off state.
    svg_size: QSize, optional
        The display size of the SVG, defaults to filling the entire size of the widget.
    """

    def __init__(self, on: str, off: str, svg_size: str = None):
        super().__init__()

        # Set layout
        layout = QHBoxLayout(self)
        self.setLayout(layout)

        # Remove margins and spacing
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Add SVG icon and set its size
        self.icon = load_icon(normal=on, normal_off=off)
        self.setIcon(self.icon)
        self.setIconSize(svg_size) if svg_size else self.setIconSize(QSize())

        # Make this a toggle button
        self.setCheckable(True)

    def enable(self) -> None:
        self.setEnabled(True)

    def disable(self) -> None:
        self.setEnabled(False)

    def set_icon(self, on: str, off: str) -> None:
        self.icon = load_icon(normal=on, normal_off=off)
        self.setIcon(self.icon)


class SvgPushButton(QPushButton):
    """
    A widget used to display the contents of Scalable Vector Graphics (SVG) files provided for
    associated user action modes, see https://doc.qt.io/qt-5/qicon.html#Mode-enum.

    Parameters
    ----------
    normal: str
        The name of the SVG file to add to the button for QIcon.Normal mode.
    disabled: str, optional
        The name of the SVG file to add to the button for QIcon.Disabled mode.
    active: str, optional
        The name of the SVG file to add to the button for QIcon.Active mode.
    selected: str, optional
        The name of the SVG file to add to the button for QIcon.Selected mode.
    svg_size: QSize, optional
        The display size of the SVG, defaults to filling the entire size of the widget.
    """

    def __init__(
        self,
        normal: str,
        disabled: str = None,
        active: str = None,
        selected: str = None,
        svg_size: str = None,
    ) -> None:
        super().__init__()

        # Set layout
        layout = QHBoxLayout(self)
        self.setLayout(layout)

        # Remove margins and spacing
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Add SVG icon and set its size
        self.icon = load_icon(
            normal=normal,
            disabled=disabled,
            active=active,
            selected=selected,
            disabled_off=disabled)
        self.setIcon(self.icon)
        self.setIconSize(svg_size) if svg_size else self.setIconSize(QSize())

    def enable(self) -> None:
        self.setEnabled(True)

    def disable(self) -> None:
        self.setEnabled(False)


class SvgLabel(QLabel):
    """
    A widget used to display the contents of a Scalable Vector Graphics (SVG) file.

    Parameters
    ----------
    filename: str
        The name of the SVG file to add to the label.
    svg_size: QSize, optional
        The display size of the SVG, defaults to filling the entire size of the widget.
    """

    def __init__(self, filename: str, svg_size: str = None) -> None:
        super().__init__()

        # Remove margins and spacing
        layout = QHBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)
        self.setLayout(layout)

        # Add SVG and set its size
        self.svg = load_svg(filename)
        self.svg.setFixedSize(svg_size) if svg_size else self.svg.setFixedSize(QSize())
        layout.addWidget(self.svg)

    def update_image(self, filename: str, svg_size: str = None) -> None:
        self.svg = load_svg(filename)
        self.svg.setFixedSize(svg_size) if svg_size else self.svg.setFixedSize(QSize())
        child = self.layout().takeAt(0)
        if child and child.widget():
            child.widget().deleteLater()
        self.layout().addWidget(self.svg)


class SecureQLabel(QLabel):
    def __init__(
        self,
        text: str = "",
        parent: QWidget = None,
        flags: Union[Qt.WindowFlags, Qt.WindowType] = Qt.WindowFlags(),
    ):
        super().__init__(parent, flags)
        self.setWordWrap(True)
        self.setText(text)

    def setText(self, text: str) -> None:
        self.setTextFormat(Qt.PlainText)
        # Wraps text at default of 70 characters.
        wrapped = "\n".join(textwrap.wrap(text))
        super().setText(wrapped)
