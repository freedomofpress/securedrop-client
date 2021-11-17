"""
Graphical user interface (GUI) elements.

This package contains mostly Qt widgets, some of them specific
to SecuredDrop.

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

# Expose GUI elements without exposing the package structure
from securedrop_client.gui.buttons import SDPushButton  # noqa: F401
from securedrop_client.gui.dialogs import SDModalDialog  # noqa: F401
from securedrop_client.gui.misc import (  # noqa: F401
    SecureQLabel,
    SvgLabel,
    SvgPushButton,
    SvgToggleButton,
)
