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
from typing import Dict, List, Optional

import sqlalchemy.orm.exc
from PyQt5.QtCore import Qt, QTimer, pyqtSignal, pyqtSlot
from PyQt5.QtGui import QResizeEvent
from PyQt5.QtWidgets import QListWidget, QVBoxLayout

from securedrop_client import state
from securedrop_client.db import Source
from securedrop_client.gui.unsorted.source_list_widget_item import SourceListWidgetItem
from securedrop_client.gui.unsorted.source_widget import SourceWidget
from securedrop_client.logic import Controller
from securedrop_client.storage import source_exists

logger = logging.getLogger(__name__)


class SourceList(QListWidget):
    """
    Displays the list of sources.
    """

    source_selection_changed = pyqtSignal(state.SourceId)
    source_selection_cleared = pyqtSignal()

    NUM_SOURCES_TO_ADD_AT_A_TIME = 32
    INITIAL_UPDATE_SCROLLBAR_WIDTH = 20

    source_selected = pyqtSignal(str)
    adjust_preview = pyqtSignal(int)

    def __init__(self) -> None:
        super().__init__()

        self.setObjectName("SourceList")
        self.setUniformItemSizes(True)

        # Set layout.
        layout = QVBoxLayout(self)
        self.setLayout(layout)

        # Disable horizontal scrollbar for SourceList widget
        self.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)

        # Enable ordering.
        self.setSortingEnabled(True)

        # To hold references to SourceListWidgetItem instances indexed by source UUID.
        self.source_items: Dict[str, SourceListWidgetItem] = {}

        self.itemSelectionChanged.connect(self._on_item_selection_changed)

    def resizeEvent(self, event: QResizeEvent) -> None:
        self.adjust_preview.emit(event.size().width())
        super().resizeEvent(event)

    def setup(self, controller: Controller) -> None:
        self.controller = controller
        self.controller.reply_succeeded.connect(self.set_snippet)
        self.controller.message_ready.connect(self.set_snippet)
        self.controller.reply_ready.connect(self.set_snippet)
        self.controller.file_ready.connect(self.set_snippet)
        self.controller.file_missing.connect(self.set_snippet)
        self.controller.message_download_failed.connect(self.set_snippet)
        self.controller.reply_download_failed.connect(self.set_snippet)

    def update_sources(self, sources: List[Source]) -> List[str]:
        """
        Update the list with the passed in list of sources.
        """
        sources_to_update = []
        sources_to_add = {}
        for source in sources:
            try:
                if source.uuid in self.source_items:
                    sources_to_update.append(source.uuid)
                else:
                    sources_to_add[source.uuid] = source
            except sqlalchemy.exc.InvalidRequestError as e:
                logger.debug(e)
                continue

        # Delete widgets for sources not in the supplied sourcelist
        deleted_uuids = []
        sources_to_delete = [
            self.source_items[uuid] for uuid in self.source_items if uuid not in sources_to_update
        ]
        for source_item in sources_to_delete:
            if source_item.isSelected():
                self.setCurrentItem(None)

            source_widget = self.itemWidget(source_item)
            self.takeItem(self.row(source_item))
            assert isinstance(source_widget, SourceWidget)
            if source_widget.source_uuid in self.source_items:
                del self.source_items[source_widget.source_uuid]

            deleted_uuids.append(source_widget.source_uuid)
            source_widget.deleteLater()

        # Update the remaining widgets
        for i in range(self.count()):
            source_widget = self.itemWidget(self.item(i))

            if not source_widget:
                continue

            assert isinstance(source_widget, SourceWidget)
            source_widget.reload()

        # Add widgets for new sources
        for uuid in sources_to_add:
            source_widget = SourceWidget(
                self.controller, sources_to_add[uuid], self.source_selected, self.adjust_preview
            )
            source_item = SourceListWidgetItem(self)
            source_item.setSizeHint(source_widget.sizeHint())
            self.insertItem(0, source_item)
            self.setItemWidget(source_item, source_widget)
            self.source_items[uuid] = source_item
            self.adjust_preview.emit(self.width() - self.INITIAL_UPDATE_SCROLLBAR_WIDTH)

        # Re-sort SourceList to make sure the most recently-updated sources appear at the top
        self.sortItems(Qt.DescendingOrder)

        # Return uuids of source widgets that were deleted so we can later delete the corresponding
        # conversation widgets
        return deleted_uuids

    def initial_update(self, sources: List[Source]) -> None:
        """
        Initialise the list with the passed in list of sources.
        """
        self.add_source(sources)

    def add_source(self, sources: List[Source], slice_size: int = 1) -> None:
        """
        Add a slice of sources, and if necessary, reschedule the addition of
        more sources.
        """

        def schedule_source_management(slice_size: int = slice_size) -> None:
            if not sources:
                self.adjust_preview.emit(self.width() - self.INITIAL_UPDATE_SCROLLBAR_WIDTH)
                return

            # Process the remaining "slice_size" number of sources.
            sources_slice = sources[:slice_size]
            for source in sources_slice:
                try:
                    source_uuid = source.uuid
                    source_widget = SourceWidget(
                        self.controller, source, self.source_selected, self.adjust_preview
                    )
                    source_item = SourceListWidgetItem(self)
                    source_item.setSizeHint(source_widget.sizeHint())
                    self.insertItem(0, source_item)
                    self.setItemWidget(source_item, source_widget)
                    self.source_items[source_uuid] = source_item
                except sqlalchemy.exc.InvalidRequestError as e:
                    logger.debug(e)

            # Re-sort SourceList to make sure the most recently-updated sources appear at the top
            self.sortItems(Qt.DescendingOrder)

            # ATTENTION! 32 is an arbitrary number arrived at via
            # experimentation. It adds plenty of sources, but doesn't block
            # for a noticable amount of time.
            new_slice_size = min(self.NUM_SOURCES_TO_ADD_AT_A_TIME, slice_size * 2)
            # Call add_source again for the remaining sources.
            self.add_source(sources[slice_size:], new_slice_size)

        # Schedule the closure defined above in the next iteration of the
        # Qt event loop (thus unblocking the UI).
        QTimer.singleShot(1, schedule_source_management)

    def get_selected_source(self) -> Optional[Source]:
        if not self.selectedItems():
            return None

        source_item = self.selectedItems()[0]
        source_widget = self.itemWidget(source_item)
        assert isinstance(source_widget, SourceWidget)
        if source_widget and source_exists(self.controller.session, source_widget.source_uuid):
            return source_widget.source
        return None  # pragma: nocover

    def get_source_widget(self, source_uuid: str) -> Optional[SourceWidget]:
        """
        First try to get the source widget from the cache, then look for it in the SourceList.
        """
        try:
            source_item = self.source_items[source_uuid]
            source_widget = self.itemWidget(source_item)
            assert isinstance(source_widget, SourceWidget)
            return source_widget
        except KeyError:
            pass

        for i in range(self.count()):
            list_item = self.item(i)
            source_widget = self.itemWidget(list_item)
            assert isinstance(source_widget, SourceWidget)
            if source_widget and source_widget.source_uuid == source_uuid:
                return source_widget

        return None

    @pyqtSlot(str, str, str)
    def set_snippet(self, source_uuid: str, collection_item_uuid: str, content: str) -> None:
        """
        Set the source widget's preview snippet with the supplied content.

        Note: The signal's `collection_item_uuid` is not needed for setting the preview snippet. It
        is used by other signal handlers.
        """
        source_widget = self.get_source_widget(source_uuid)
        if source_widget:
            source_widget.set_snippet(source_uuid, collection_item_uuid, content)

    @pyqtSlot()
    def _on_item_selection_changed(self) -> None:
        source = self.get_selected_source()
        if source is not None:
            self.source_selection_changed.emit(state.SourceId(source.uuid))
        else:
            self.source_selection_cleared.emit()
