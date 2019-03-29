"""
Functions needed to work with non-code resources such as images (icons and SVG
files) and CSS (for configuring the look of the UI).

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
from pkg_resources import resource_filename, resource_string
from PyQt5.QtGui import QPixmap, QIcon
from PyQt5.QtSvg import QSvgWidget
from PyQt5.QtCore import Qt, QDir, QSize
from PyQt5.QtWidgets import QPushButton

# Add the images and CSS directories to the search path.
QDir.addSearchPath('images', resource_filename(__name__, 'images'))
QDir.addSearchPath('css', resource_filename(__name__, 'css'))


def path(name, resource_dir="images/"):
    """
    Return the filename for the referenced image.

    Qt uses unix path conventions.
    """
    return resource_filename(__name__, resource_dir + name)


def load_icon(name):
    """
    Return a QIcon representation of a file in the resources.
    """
    return QIcon(path(name))


def load_svg(name):
    """
    Return a QSvgWidget representation of a file in the resources.
    """
    return QSvgWidget(path(name))


def load_image(name):
    """
    Return a QPixmap representation of a file in the resources.
    """
    return QPixmap(path(name))


def load_css(name):
    """
    Return the contents of the referenced CSS file in the resources.
    """
    return resource_string(__name__, "css/" + name).decode('utf-8')


def load_icon_button(normal: str, disabled=None, active=None, selected=None) -> QPushButton:
    icon = QIcon()

    pixmap = load_image(normal)
    scaled = pixmap.scaled(18, 18, Qt.KeepAspectRatio, transformMode=Qt.SmoothTransformation)
    icon.addPixmap(scaled, QIcon.Normal)

    if disabled:
        pixmap = load_image(disabled)
        scaled = pixmap.scaled(18, 18, Qt.KeepAspectRatio, transformMode=Qt.SmoothTransformation)
        icon.addPixmap(scaled, QIcon.Disabled)

    if active:
        pixmap = load_image(active)
        scaled = pixmap.scaled(18, 18, Qt.KeepAspectRatio, transformMode=Qt.SmoothTransformation)
        icon.addPixmap(scaled, QIcon.Active)

    if selected:
        pixmap = load_image(selected)
        scaled = pixmap.scaled(18, 18, Qt.KeepAspectRatio, transformMode=Qt.SmoothTransformation)
        icon.addPixmap(scaled, QIcon.Selected)

    icon_button = QPushButton()
    icon_button.setIconSize(QSize(18, 18))
    icon_button.setIcon(icon)

    return icon_button
