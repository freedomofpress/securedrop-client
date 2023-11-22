"""
Contains the main widgets used by the client to display things in the UI.

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
from __future__ import annotations

import logging

from PyQt5.QtCore import QEvent, QObject, QSize, QTimer, pyqtSlot

from securedrop_client.gui.base import SvgToggleButton
from securedrop_client.logic import Controller
from securedrop_client.resources import load_icon

logger = logging.getLogger(__name__)


class StarToggleButton(SvgToggleButton):
    """
    A button that shows whether or not a source is starred
    """

    def __init__(self, controller: Controller, source_uuid: str, is_starred: bool) -> None:
        super().__init__(on="star_on.svg", off="star_off.svg", svg_size=QSize(16, 16))

        self.controller = controller
        self.source_uuid = source_uuid
        self.is_starred = is_starred
        self.pending_count = 0
        self.wait_until_next_sync = False

        self.controller.authentication_state.connect(self.on_authentication_changed)
        self.controller.star_update_failed.connect(self.on_star_update_failed)
        self.controller.star_update_successful.connect(self.on_star_update_successful)
        self.installEventFilter(self)

        self.setObjectName("StarToggleButton")
        self.setFixedSize(QSize(20, 20))

        self.pressed.connect(self.on_pressed)
        self.setCheckable(True)
        self.setChecked(self.is_starred)

        if not self.controller.is_authenticated:
            self.disable_toggle()

    def disable_toggle(self) -> None:
        """
        Unset `checkable` so that the star cannot be toggled.

        Disconnect the `pressed` signal from previous handler and connect it to the offline handler.
        """
        self.pressed.disconnect()
        self.pressed.connect(self.on_pressed_offline)

        # If the source is starred, we must update the icon so that the off state continues to show
        # the source as starred. We could instead disable the button, which will continue to show
        # the star as checked, but Qt will also gray out the star, which we don't want.
        if self.is_starred:
            self.set_icon(on="star_on.svg", off="star_on.svg")
        self.setCheckable(False)

    def enable_toggle(self) -> None:
        """
        Enable the widget.

        Disconnect the pressed signal from previous handler, set checkable so that the star can be
        toggled, and connect to the online toggle handler.

        Note: We must update the icon in case it was modified after being disabled.
        """
        self.pressed.disconnect()
        self.pressed.connect(self.on_pressed)
        self.setCheckable(True)
        self.set_icon(on="star_on.svg", off="star_off.svg")  # Undo icon change from disable_toggle

    def eventFilter(self, obj: QObject, event: QEvent) -> bool:
        """
        If the button is checkable then we show a hover state.
        """
        if not self.isCheckable():
            return QObject.event(obj, event)

        t = event.type()
        if t == QEvent.HoverEnter:
            self.setIcon(load_icon("star_hover.svg"))
        elif t == QEvent.HoverLeave or t == QEvent.MouseButtonPress:
            self.set_icon(on="star_on.svg", off="star_off.svg")

        return QObject.event(obj, event)

    @pyqtSlot(bool)
    def on_authentication_changed(self, authenticated: bool) -> None:
        """
        Set up handlers based on whether or not the user is authenticated. Connect to 'pressed'
        event instead of 'toggled' event when not authenticated because toggling will be disabled.
        """
        if authenticated:
            self.pending_count = 0
            self.enable_toggle()
            self.setChecked(self.is_starred)
        else:
            self.disable_toggle()

    @pyqtSlot()
    def on_pressed(self) -> None:
        """
        Tell the controller to make an API call to update the source's starred field.
        """
        self.controller.update_star(self.source_uuid, self.isChecked())
        self.is_starred = not self.is_starred
        self.pending_count = self.pending_count + 1
        self.wait_until_next_sync = True

    @pyqtSlot()
    def on_pressed_offline(self) -> None:
        """
        Show error message when not authenticated.
        """
        self.controller.on_action_requiring_login()

    @pyqtSlot(bool)
    def update(self, is_starred: bool) -> None:
        """
        If star was updated via the Journalist Interface or by another instance of the client, then
        self.is_starred will not match the server and will need to be updated.
        """
        if not self.controller.is_authenticated:
            return

        # Wait until ongoing star jobs are finished before checking if it matches with the server
        if self.pending_count > 0:
            return

        # Wait until next sync to avoid the possibility of updating the star with outdated source
        # information in case the server just received the star request.
        if self.wait_until_next_sync:
            self.wait_until_next_sync = False
            return

        if self.is_starred != is_starred:
            self.is_starred = is_starred
            self.setChecked(self.is_starred)

    @pyqtSlot(str, bool)
    def on_star_update_failed(self, source_uuid: str, is_starred: bool) -> None:
        """
        If the star update failed to update on the server, toggle back to previous state.
        """
        if self.source_uuid == source_uuid:
            self.is_starred = is_starred
            self.pending_count = self.pending_count - 1
            QTimer.singleShot(250, lambda: self.setChecked(self.is_starred))

    @pyqtSlot(str)
    def on_star_update_successful(self, source_uuid: str) -> None:
        """
        If the star update succeeded, set pending to False so the sync can update the star field
        """
        if self.source_uuid == source_uuid:
            self.pending_count = self.pending_count - 1
