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
from datetime import datetime
from gettext import gettext as _
from typing import Optional

import sqlalchemy.orm.exc
from PyQt5.QtCore import QSize, Qt, pyqtBoundSignal, pyqtSlot
from PyQt5.QtGui import QCursor
from PyQt5.QtWidgets import QGridLayout, QHBoxLayout, QLabel, QSpacerItem, QWidget

from securedrop_client.db import Source
from securedrop_client.gui.base import SvgLabel
from securedrop_client.gui.datetime_helpers import format_datetime_local
from securedrop_client.gui.unsorted.source_preview import SourcePreview
from securedrop_client.gui.unsorted.source_widget_deletion_indicator import (
    SourceWidgetDeletionIndicator,
)
from securedrop_client.gui.unsorted.star_toggle_button import StarToggleButton
from securedrop_client.logic import Controller
from securedrop_client.resources import load_css

logger = logging.getLogger(__name__)


class SourceWidget(QWidget):
    """
    Used to display summary information about a source in the list view.
    """

    TOP_MARGIN = 11
    BOTTOM_MARGIN = 7
    SIDE_MARGIN = 10
    SPACER = 14
    BOTTOM_SPACER = 11
    STAR_WIDTH = 20
    TIMESTAMP_WIDTH = 60

    SOURCE_NAME_CSS = load_css("source_name.css")
    SOURCE_PREVIEW_CSS = load_css("source_preview.css")
    SOURCE_TIMESTAMP_CSS = load_css("source_timestamp.css")

    CONVERSATION_DELETED_TEXT = _("\u2014 All files and messages deleted for this source \u2014")

    def __init__(
        self,
        controller: Controller,
        source: Source,
        source_selected_signal: pyqtBoundSignal,
        adjust_preview: pyqtBoundSignal,
    ):
        super().__init__()

        self.controller = controller
        self.controller.sync_started.connect(self._on_sync_started)
        self.controller.conversation_deleted.connect(self._on_conversation_deleted)
        controller.conversation_deletion_successful.connect(
            self._on_conversation_deletion_successful
        )
        self.controller.conversation_deletion_failed.connect(self._on_conversation_deletion_failed)
        self.controller.source_deleted.connect(self._on_source_deleted)
        self.controller.source_deletion_failed.connect(self._on_source_deletion_failed)
        self.controller.authentication_state.connect(self._on_authentication_changed)
        source_selected_signal.connect(self._on_source_selected)
        adjust_preview.connect(self._on_adjust_preview)

        self.source: Source = source
        self.seen = self.source.seen
        self.source_uuid: str = self.source.uuid
        self.last_updated: sqlalchemy.DateTime = self.source.last_updated
        self.selected = False
        self.deletion_scheduled_timestamp = datetime.utcnow()
        self.sync_started_timestamp = datetime.utcnow()

        self.deleting_conversation = False
        self.deleting = False

        self.setCursor(QCursor(Qt.PointingHandCursor))

        retain_space = self.sizePolicy()
        retain_space.setRetainSizeWhenHidden(True)
        self.star = StarToggleButton(self.controller, self.source_uuid, source.is_starred)
        self.star.setSizePolicy(retain_space)
        self.star.setFixedWidth(self.STAR_WIDTH)
        self.name = QLabel()
        self.name.setObjectName("SourceWidget_name")
        self.preview = SourcePreview()
        self.preview.setObjectName("SourceWidget_preview")
        self.deletion_indicator = SourceWidgetDeletionIndicator()

        self.paperclip = SvgLabel("paperclip.svg", QSize(11, 17))  # Set to size provided in the svg
        self.paperclip.setObjectName("SourceWidget_paperclip")
        self.paperclip.setFixedSize(QSize(11, 17))
        self.paperclip.setSizePolicy(retain_space)

        self.paperclip_disabled = SvgLabel("paperclip-disabled.svg", QSize(11, 17))
        self.paperclip_disabled.setObjectName("SourceWidget_paperclip")
        self.paperclip_disabled.setFixedSize(QSize(11, 17))
        self.paperclip_disabled.setSizePolicy(retain_space)
        self.paperclip_disabled.hide()

        self.timestamp = QLabel()
        self.timestamp.setSizePolicy(retain_space)
        self.timestamp.setFixedWidth(self.TIMESTAMP_WIDTH)
        self.timestamp.setObjectName("SourceWidget_timestamp")

        # Create source_widget:
        # -------------------------------------------------------------------
        # | ------ | -------- | ------                   | -----------      |
        # | |star| | |spacer| | |name|                   | |paperclip|      |
        # | ------ | -------- | ------                   | -----------      |
        # -------------------------------------------------------------------
        # |        |          | ---------                | -----------      |
        # |        |          | |preview|                | |timestamp|      |
        # |        |          | ---------                | -----------      |
        # ------------------------------------------- -----------------------
        # Column 0, 1, and 3 are fixed. Column 2 stretches.
        self.source_widget = QWidget()
        self.source_widget.setObjectName("SourceWidget_container")
        source_widget_layout = QGridLayout()
        source_widget_layout.setSpacing(0)
        source_widget_layout.setContentsMargins(0, self.TOP_MARGIN, 0, self.BOTTOM_MARGIN)
        source_widget_layout.addWidget(self.star, 0, 0, 1, 1)
        self.spacer = QWidget()
        self.spacer.setFixedWidth(self.SPACER)
        source_widget_layout.addWidget(self.spacer, 0, 1, 1, 1)
        source_widget_layout.addWidget(self.name, 0, 2, 1, 1)
        source_widget_layout.addWidget(self.paperclip, 0, 3, 1, 1)
        source_widget_layout.addWidget(self.paperclip_disabled, 0, 3, 1, 1)
        source_widget_layout.addWidget(self.preview, 1, 2, 1, 1, alignment=Qt.AlignLeft)
        source_widget_layout.addWidget(self.deletion_indicator, 1, 2, 1, 1)
        source_widget_layout.addWidget(self.timestamp, 1, 3, 1, 1)
        source_widget_layout.addItem(QSpacerItem(self.BOTTOM_SPACER, self.BOTTOM_SPACER))
        self.source_widget.setLayout(source_widget_layout)
        layout = QHBoxLayout(self)
        self.setLayout(layout)
        layout.setContentsMargins(self.SIDE_MARGIN, 0, self.SIDE_MARGIN, 0)
        layout.setSpacing(0)
        layout.addWidget(self.source_widget)

        self.reload()

    @pyqtSlot(int)
    def _on_adjust_preview(self, width: int) -> None:
        self.setFixedWidth(width)
        self.preview.adjust_preview(width)

    def reload(self) -> None:
        """
        Updates the displayed values with the current values from self.source.
        """
        # If the account or conversation is being deleted, do not update the source widget
        if self.deleting or self.deleting_conversation:
            return

        # If the sync started before the deletion finished, then the sync is stale and we do
        # not want to update the source widget.
        if self.sync_started_timestamp < self.deletion_scheduled_timestamp:
            return

        try:
            self.controller.session.refresh(self.source)
            self.last_updated = self.source.last_updated
            self.timestamp.setText(_(format_datetime_local(self.source.last_updated)))
            self.name.setText(self.source.journalist_designation)

            self.set_snippet(self.source_uuid)

            if self.source.document_count == 0:
                self.paperclip.hide()
                self.paperclip_disabled.hide()

            if not self.source.server_collection and self.source.interaction_count > 0:
                self.preview.setProperty("class", "conversation_deleted")
            else:
                self.preview.setProperty("class", "")

            self.star.update(self.source.is_starred)

            self.end_deletion()

            if self.source.document_count == 0:
                self.paperclip.hide()
                self.paperclip_disabled.hide()

            self.star.update(self.source.is_starred)

            # When not authenticated we always show the source as having been seen
            self.seen = True if not self.controller.is_authenticated else self.source.seen
            self.update_styles()
        except sqlalchemy.exc.InvalidRequestError as e:
            logger.debug(f"Could not update SourceWidget for source {self.source_uuid}: {e}")

    @pyqtSlot(str, str, str)
    def set_snippet(
        self, source_uuid: str, collection_uuid: Optional[str] = None, content: Optional[str] = None
    ) -> None:
        """
        Update the preview snippet if the source_uuid matches our own.
        """
        if source_uuid != self.source_uuid:
            return

        # If the account or conversation is being deleted, do not update the source widget
        if self.deleting or self.deleting_conversation:
            return

        # If the source collection is empty yet the interaction_count is greater than zero, then we
        # known that the conversation has been deleted.
        if not self.source.server_collection:
            if self.source.interaction_count > 0:
                self.set_snippet_to_conversation_deleted()
        else:
            last_activity = self.source.server_collection[-1]
            if collection_uuid and collection_uuid != last_activity.uuid:
                return

            self.preview.setProperty("class", "")
            self.preview.setText(content) if content else self.preview.setText(str(last_activity))
            self.preview.adjust_preview(self.width())
            self.update_styles()

    def set_snippet_to_conversation_deleted(self) -> None:
        self.preview.setProperty("class", "conversation_deleted")
        self.preview.setText(self.CONVERSATION_DELETED_TEXT)
        self.preview.adjust_preview(self.width())
        self.update_styles()

    def update_styles(self) -> None:
        if self.seen:
            self.name.setStyleSheet("")
            if self.selected:
                self.name.setObjectName("SourceWidget_name_selected")
            else:
                self.name.setObjectName("SourceWidget_name")
            self.name.setStyleSheet(self.SOURCE_NAME_CSS)

            self.timestamp.setStyleSheet("")
            self.timestamp.setObjectName("SourceWidget_timestamp")
            self.timestamp.setStyleSheet(self.SOURCE_TIMESTAMP_CSS)

            self.preview.setStyleSheet("")
            self.preview.setObjectName("SourceWidget_preview")
            self.preview.setStyleSheet(self.SOURCE_PREVIEW_CSS)
        else:
            self.name.setStyleSheet("")
            self.name.setObjectName("SourceWidget_name_unread")
            self.name.setStyleSheet(self.SOURCE_NAME_CSS)

            self.timestamp.setStyleSheet("")
            self.timestamp.setObjectName("SourceWidget_timestamp_unread")
            self.timestamp.setStyleSheet(self.SOURCE_TIMESTAMP_CSS)

            self.preview.setStyleSheet("")
            self.preview.setObjectName("SourceWidget_preview_unread")
            self.preview.setStyleSheet(self.SOURCE_PREVIEW_CSS)

    @pyqtSlot(bool)
    def _on_authentication_changed(self, authenticated: bool) -> None:
        """
        When the user logs out, show source as seen.
        """
        if not authenticated:
            self.seen = True
            self.update_styles()

    @pyqtSlot(str)
    def _on_source_selected(self, selected_source_uuid: str) -> None:
        """
        Show selected widget as having been seen.
        """
        if self.source_uuid == selected_source_uuid:
            self.seen = True
            self.selected = True
            self.update_styles()
        else:
            self.selected = False
            self.update_styles()

    @pyqtSlot(datetime)
    def _on_sync_started(self, timestamp: datetime) -> None:
        self.sync_started_timestamp = timestamp

    @pyqtSlot(str)
    def _on_conversation_deleted(self, source_uuid: str) -> None:
        if self.source_uuid == source_uuid:
            self.start_conversation_deletion()

    @pyqtSlot(str, datetime)
    def _on_conversation_deletion_successful(self, source_uuid: str, timestamp: datetime) -> None:
        if self.source_uuid == source_uuid:
            self.deletion_scheduled_timestamp = timestamp
            self.set_snippet_to_conversation_deleted()
            self.end_conversation_deletion()

    @pyqtSlot(str)
    def _on_conversation_deletion_failed(self, source_uuid: str) -> None:
        if self.source_uuid == source_uuid:
            self.end_conversation_deletion()

    @pyqtSlot(str)
    def _on_source_deleted(self, source_uuid: str) -> None:
        if self.source_uuid == source_uuid:
            self.start_account_deletion()

    @pyqtSlot(str)
    def _on_source_deletion_failed(self, source_uuid: str) -> None:
        if self.source_uuid == source_uuid:
            self.end_account_deletion()

    def end_account_deletion(self) -> None:
        self.end_deletion()
        self.star.show()
        self.name.setProperty("class", "")
        self.timestamp.setProperty("class", "")
        self.update_styles()
        self.deleting = False

    def end_conversation_deletion(self) -> None:
        self.end_deletion()
        self.deleting_conversation = False

    def end_deletion(self) -> None:
        self.deletion_indicator.stop()
        self.update_styles()
        self.preview.show()
        self.timestamp.show()
        self.paperclip_disabled.hide()
        if self.source.document_count != 0:
            self.paperclip.show()

    def start_account_deletion(self) -> None:
        self.deleting = True
        self.start_deletion()
        self.name.setProperty("class", "deleting")
        self.timestamp.setProperty("class", "deleting")
        self.star.hide()
        self.update_styles()

    def start_conversation_deletion(self) -> None:
        self.deleting_conversation = True
        self.start_deletion()

    def start_deletion(self) -> None:
        self.preview.hide()
        self.paperclip.hide()
        if self.source.document_count != 0:
            self.paperclip_disabled.show()
        self.deletion_indicator.start()
