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
import os

from pkg_resources import resource_filename, resource_string
from PyQt5.QtGui import QPixmap, QIcon, QFontDatabase
from PyQt5.QtSvg import QSvgWidget
from PyQt5.QtCore import QDir

# Add resource directories to the search path.
QDir.addSearchPath('images', resource_filename(__name__, 'images'))
QDir.addSearchPath('css', resource_filename(__name__, 'css'))


def path(name: str, resource_dir: str = "images/") -> str:
    """
    Return the filename for the referenced image.

    Qt uses unix path conventions.
    """
    return resource_filename(__name__, resource_dir + name)


def load_font(font_folder_name: str) -> None:
    directory = resource_filename(__name__, 'fonts/') + font_folder_name
    for filename in os.listdir(directory):
        if filename.endswith(".ttf"):
            QFontDatabase.addApplicationFont(directory + '/' + filename)


def load_icon(
    normal: str,
    disabled: str = None,
    active: str = None,
    selected: str = None,
    normal_off: str = None,
    disabled_off: str = None,
    active_off: str = None,
    selected_off: str = None,
) -> QIcon:
    """
    Add the contents of Scalable Vector Graphics (SVG) files provided for associated icon modes and
    states, see https://doc.qt.io/qt-5/qicon.html#Mode-enum. If the widget containing this icon is
    set to checkable, then the *_off states will be displayed.

    Parameters
    ----------
    normal: str
        The name of the SVG file to add to the icon for QIcon.Normal mode.
    disabled: str or None, optional
        The name of the SVG file to add to the icon for QIcon.Disabled mode.
    active: str, optional
        The name of the SVG file to add to the icon for QIcon.Active mode.
    selected: str, optional
        The name of the SVG file to add to the icon for QIcon.Selected mode.
    normal_off: str
        The name of the SVG file to add to the icon for QIcon.Normal mode.
    disabled_off: str or None, optional
        The name of the SVG file to add to the icon for QIcon.Disabled mode.
    active_off: str, optional
        The name of the SVG file to add to the icon for QIcon.Active mode.
    selected_off: str, optional
        The name of the SVG file to add to the icon for QIcon.Selected mode.

    Returns
    -------
    QIcon
        The icon that displays the contents of the SVG files.

    """

    icon = QIcon()

    icon.addFile(path(normal), mode=QIcon.Normal, state=QIcon.On)

    if disabled:
        icon.addFile(path(disabled), mode=QIcon.Disabled, state=QIcon.On)

    if active:
        icon.addFile(path(active), mode=QIcon.Active, state=QIcon.On)

    if selected:
        icon.addFile(path(selected), mode=QIcon.Selected, state=QIcon.On)

    if normal_off:
        icon.addFile(path(normal_off), mode=QIcon.Normal, state=QIcon.Off)

    if disabled_off:
        icon.addFile(path(disabled_off), mode=QIcon.Disabled, state=QIcon.Off)

    if active_off:
        icon.addFile(path(active_off), mode=QIcon.Active, state=QIcon.Off)

    if selected_off:
        icon.addFile(path(selected_off), mode=QIcon.Selected, state=QIcon.Off)

    return icon


def load_svg(name: str) -> QSvgWidget:
    """
    Return a QSvgWidget representation of a file in the resources.
    """
    return QSvgWidget(path(name))


def load_image(name: str) -> QPixmap:
    """
    Return a QPixmap representation of a file in the resources.
    """
    return QPixmap(path(name))


def load_css(name: str) -> str:
    """
    Return the contents of the referenced CSS file in the resources.
    """
    return resource_string(__name__, "css/" + name).decode('utf-8')
