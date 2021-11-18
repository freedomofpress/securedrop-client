"""
SecureDrop Menu Bar

A menu bar inspired by the behavior of the menu bar of Firefox.
It is designed to be unobstrusive, but remains conformant with
the Freedesktop and Qubes OS conventions for increased accessibility.

This menu bar shoudl allow journalists to:

- Discover all the actions available to them at any given time
- Trigger any available action via their keyboard, or any input method
  capable of emulating key events.

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
from PyQt5.QtCore import Qt
from PyQt5.QtGui import QFocusEvent, QKeyEvent
from PyQt5.QtWidgets import QMenuBar, QWidget


class SDMenuBar(QMenuBar):
    """A menu bar that hides itself automatically when out of focus."""

    def __init__(self, parent: QWidget) -> None:
        super().__init__(parent)
        self.hide()

    def focusOutEvent(self, event: QFocusEvent) -> bool:
        """Hide the menu bar unless the focus went to a menu."""
        if event.reason() != Qt.PopupFocusReason:
            self.hide()
        return super().focusOutEvent(event)

    def keyPressEvent(self, event: QKeyEvent) -> None:
        """Show the menu bar and grab focus when Alt is pressed. Close it on Alt or Escape."""
        if event.key() == Qt.Key_Alt:
            if self.isVisible():
                self.hide()
                self.clearFocus()
                return None
            else:
                self.show()
                self.setFocus()
                return None
        if event.key() == Qt.Key_Escape:
            self.hide()
            self.clearFocus()
            return None
        return super().keyPressEvent(event)
