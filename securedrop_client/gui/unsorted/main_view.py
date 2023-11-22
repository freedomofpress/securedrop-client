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
from typing import List, Optional

import sqlalchemy.orm.exc
from PyQt5.QtWidgets import QHBoxLayout, QVBoxLayout, QWidget

from securedrop_client import state
from securedrop_client.db import Source
from securedrop_client.gui.unsorted.empty_conversation_view import EmptyConversationView
from securedrop_client.gui.unsorted.source_conversation_wrapper import SourceConversationWrapper
from securedrop_client.gui.unsorted.source_list import SourceList
from securedrop_client.logic import Controller

logger = logging.getLogger(__name__)


class MainView(QWidget):
    """
    Represents the main content of the application (containing the source list
    and main context view).
    """

    def __init__(
        self,
        parent: Optional[QWidget],
        app_state: Optional[state.State] = None,
    ) -> None:
        super().__init__(parent)

        self._state = app_state

        # Set id and styles
        self.setObjectName("MainView")

        # Set layout
        self._layout = QHBoxLayout(self)
        self.setLayout(self._layout)

        # Set margins and spacing
        self._layout.setContentsMargins(0, 0, 0, 0)
        self._layout.setSpacing(0)

        # Create SourceList widget
        self.source_list = SourceList()
        self.source_list.itemSelectionChanged.connect(self.on_source_changed)
        if app_state is not None:
            self.source_list.source_selection_changed.connect(
                app_state.set_selected_conversation_for_source
            )
            self.source_list.source_selection_cleared.connect(app_state.clear_selected_conversation)

        # Create widgets
        self.view_holder = QWidget()
        self.view_holder.setObjectName("MainView_view_holder")
        self.view_layout = QVBoxLayout()
        self.view_holder.setLayout(self.view_layout)
        self.view_layout.setContentsMargins(0, 0, 0, 0)
        self.view_layout.setSpacing(0)
        self.empty_conversation_view = EmptyConversationView()
        self.view_layout.addWidget(self.empty_conversation_view)

        # Add widgets to layout
        self._layout.addWidget(self.source_list, stretch=1)
        self._layout.addWidget(self.view_holder, stretch=2)

        # Note: We should not delete SourceConversationWrapper when its source is unselected. This
        # is a temporary solution to keep copies of our objects since we do delete them.
        self.source_conversations = {}  # type: Dict[str, SourceConversationWrapper]

    def setup(self, controller: Controller) -> None:
        """
        Pass through the controller object to this widget.
        """
        self.controller = controller
        self.source_list.setup(controller)

    def show_sources(self, sources: List[Source]) -> None:
        """
        Update the sources list in the GUI with the supplied list of sources.
        """
        # If no sources are supplied, display the EmptyConversationView with the no-sources message.
        #
        # If there are sources but no source is selected in the GUI, display the
        # EmptyConversationView with the no-source-selected messaging.
        #
        # Otherwise, hide the EmptyConversationView.
        if not sources:
            self.empty_conversation_view.show_no_sources_message()
            self.empty_conversation_view.show()
        elif not self.source_list.get_selected_source():
            self.empty_conversation_view.show_no_source_selected_message()
            self.empty_conversation_view.show()
        else:
            self.empty_conversation_view.hide()

        # If the source list in the GUI is empty, then we will run the optimized initial update.
        # Otherwise, do a regular source list update.
        if not self.source_list.source_items:
            self.source_list.initial_update(sources)
        else:
            deleted_sources = self.source_list.update_sources(sources)
            for source_uuid in deleted_sources:
                # Then call the function to remove the wrapper and its children.
                self.delete_conversation(source_uuid)

    def on_source_changed(self) -> None:
        """
        Show conversation for the selected source.
        """
        try:
            source = self.source_list.get_selected_source()
            if not source:
                return

            self.controller.session.refresh(source)

            # Immediately show the selected source as seen in the UI and then make a request to mark
            # source as seen.
            self.source_list.source_selected.emit(source.uuid)
            self.controller.mark_seen(source)

            # Get or create the SourceConversationWrapper
            if source.uuid in self.source_conversations:
                conversation_wrapper = self.source_conversations[source.uuid]
                conversation_wrapper.conversation_view.update_conversation(  # type: ignore[has-type]  # noqa: E501
                    source.collection
                )
            else:
                conversation_wrapper = SourceConversationWrapper(
                    source, self.controller, self._state
                )
                self.source_conversations[source.uuid] = conversation_wrapper

            self.set_conversation(conversation_wrapper)
            logger.debug(
                "Set conversation to the selected source with uuid: {}".format(source.uuid)
            )

        except sqlalchemy.exc.InvalidRequestError as e:
            logger.debug(e)

    def refresh_source_conversations(self) -> None:
        """
        Refresh the selected source conversation.
        """
        try:
            source = self.source_list.get_selected_source()
            if not source:
                return
            self.controller.session.refresh(source)
            self.controller.mark_seen(source)
            conversation_wrapper = self.source_conversations[source.uuid]
            conversation_wrapper.conversation_view.update_conversation(  # type: ignore[has-type]
                source.collection
            )
        except sqlalchemy.exc.InvalidRequestError as e:
            logger.debug("Error refreshing source conversations: %s", e)

    def delete_conversation(self, source_uuid: str) -> None:
        """
        When we delete a source, we should delete its SourceConversationWrapper,
        and remove the reference to it in self.source_conversations
        """
        try:
            logger.debug("Deleting SourceConversationWrapper for {}".format(source_uuid))
            conversation_wrapper = self.source_conversations[source_uuid]
            conversation_wrapper.deleteLater()
            del self.source_conversations[source_uuid]
        except KeyError:
            logger.debug("No SourceConversationWrapper for {} to delete".format(source_uuid))

    def set_conversation(self, widget: QWidget) -> None:
        """
        Update the view holder to contain the referenced widget.
        """
        old_widget = self.view_layout.takeAt(0)

        if old_widget and old_widget.widget():
            old_widget.widget().hide()

        self.empty_conversation_view.hide()
        self.view_layout.addWidget(widget)
        widget.show()
