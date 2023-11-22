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
from typing import Union

import sqlalchemy.orm.exc
from PyQt5.QtCore import Qt, pyqtSignal, pyqtSlot
from PyQt5.QtWidgets import QVBoxLayout, QWidget

from securedrop_client.db import DraftReply, File, Message, Reply, Source, User
from securedrop_client.gui.unsorted.conversation_scroll_area import ConversationScrollArea
from securedrop_client.gui.unsorted.deleted_conversation_items_marker import (
    DeletedConversationItemsMarker,
)
from securedrop_client.gui.unsorted.deleted_conversation_marker import DeletedConversationMarker
from securedrop_client.gui.unsorted.file_widget import FileWidget
from securedrop_client.gui.unsorted.message_widget import MessageWidget
from securedrop_client.gui.unsorted.reply_widget import ReplyWidget
from securedrop_client.gui.unsorted.speech_bubble import SpeechBubble
from securedrop_client.logic import Controller

logger = logging.getLogger(__name__)


class ConversationView(QWidget):
    """
    Renders a conversation.
    """

    conversation_updated = pyqtSignal()

    SCROLL_BAR_WIDTH = 15

    def __init__(
        self,
        source_db_object: Source,
        controller: Controller,
    ) -> None:
        super().__init__()

        self.source = source_db_object
        self.source_uuid = source_db_object.uuid
        self.controller = controller

        self.controller.sync_started.connect(self._on_sync_started)
        controller.conversation_deletion_successful.connect(
            self._on_conversation_deletion_successful
        )

        # To hold currently displayed messages.
        self.current_messages = {}  # type: Dict[str, Union[FileWidget, MessageWidget, ReplyWidget]]

        self.deletion_scheduled_timestamp = datetime.utcnow()
        self.sync_started_timestamp = datetime.utcnow()

        self.setObjectName("ConversationView")

        # Set layout
        main_layout = QVBoxLayout()
        self.setLayout(main_layout)

        # Set margins and spacing
        main_layout.setContentsMargins(0, 0, 0, 0)
        main_layout.setSpacing(0)

        self.deleted_conversation_items_marker = DeletedConversationItemsMarker()
        self.deleted_conversation_marker = DeletedConversationMarker()
        main_layout.addWidget(self.deleted_conversation_items_marker)
        main_layout.addWidget(self.deleted_conversation_marker)

        self._scroll = ConversationScrollArea()

        # Flag to show if the current user has sent a reply. See issue #61.
        self.reply_flag = False

        # Completely unintuitive way to ensure the view remains scrolled to the bottom.
        sb = self._scroll.verticalScrollBar()
        sb.rangeChanged.connect(self.update_conversation_position)

        main_layout.addWidget(self._scroll)

        try:
            self.update_conversation(self.source.collection)
        except sqlalchemy.exc.InvalidRequestError as e:
            logger.debug("Error initializing ConversationView: %s", e)

    @pyqtSlot(datetime)
    def _on_sync_started(self, timestamp: datetime) -> None:
        self.sync_started_timestamp = timestamp

    @pyqtSlot(str, datetime)
    def _on_conversation_deletion_successful(self, source_uuid: str, timestamp: datetime) -> None:
        if self.source_uuid != source_uuid:
            return

        self.deletion_scheduled_timestamp = timestamp

        # Now that we know the deletion is scheduled, hide conversation items until they are
        # removed from the local database.
        try:
            draft_reply_exists = False
            for item in self.source.collection:
                if isinstance(item, DraftReply):
                    draft_reply_exists = True
                    continue
                item_widget = self.current_messages.get(item.uuid)
                if item_widget:
                    item_widget.hide()

            # If a draft reply exists then show the tear pattern above the draft replies.
            # Otherwise, show that the entire conversation is deleted.
            if draft_reply_exists:
                self._scroll.show()
                self.deleted_conversation_items_marker.show()
                self.deleted_conversation_marker.hide()
            else:
                self._scroll.hide()
                self.deleted_conversation_items_marker.hide()
                self.deleted_conversation_marker.show()
        except sqlalchemy.exc.InvalidRequestError as e:
            logger.debug(f"Could not update ConversationView: {e}")

    def update_deletion_markers(self) -> None:
        if self.source.collection:
            self._scroll.show()
            if self.source.collection[0].file_counter > 1:
                self.deleted_conversation_marker.hide()
                self.deleted_conversation_items_marker.show()
        elif self.source.interaction_count > 0:
            self._scroll.hide()
            self.deleted_conversation_items_marker.hide()
            self.deleted_conversation_marker.show()

    def update_conversation(self, collection: list) -> None:
        """
        Given a list of conversation items that reflect the new state of the
        conversation, this method does two things:

        * Checks if the conversation item already exists in the conversation.
          If so, it checks that it's still in the same position. If it isn't,
          the item is removed from its current position and re-added at the
          new position. Then the index meta-data on the widget is updated to
          reflect this change.
        * If the item is a new item, this is created (as before) and inserted
          into the conversation at the correct index.

        Things to note, speech bubbles and files have an index attribute which
        defines where they currently are. This is the attribute that's checked
        when the new conversation state (i.e. the collection argument) is
        passed into this method in case of a mismatch between where the widget
        has been and now is in terms of its index in the conversation.
        """
        self.controller.session.refresh(self.source)

        # Keep a temporary copy of the current conversation so we can delete any
        # items corresponding to deleted items in the source collection.
        current_conversation = self.current_messages.copy()

        for index, conversation_item in enumerate(collection):
            item_widget = current_conversation.get(conversation_item.uuid)
            if item_widget:
                # FIXME: Item types cannot be defines as (FileWidget, MessageWidget, ReplyWidget)
                # because one test mocks MessageWidget.
                assert isinstance(item_widget, (FileWidget, SpeechBubble))
                current_conversation.pop(conversation_item.uuid)
                if item_widget.index != index:
                    # The existing widget is out of order.
                    # Remove / re-add it and update index details.
                    self._scroll.remove_widget_from_conversation(item_widget)
                    item_widget.index = index
                    if isinstance(item_widget, ReplyWidget):
                        self._scroll.add_widget_to_conversation(index, item_widget, Qt.AlignRight)
                    else:
                        self._scroll.add_widget_to_conversation(index, item_widget, Qt.AlignLeft)
                # Check if text in item has changed, then update the
                # widget to reflect this change.
                if not isinstance(item_widget, FileWidget):
                    if (
                        item_widget.message.text() != conversation_item.content
                    ) and conversation_item.content:
                        item_widget.message.setText(conversation_item.content)

                    # If the item widget is not a FileWidget, retrieve the latest list of
                    # usernames of the users who have seen it.
                    item_widget.update_seen_by_list(conversation_item.seen_by_list)

                # TODO: Once the SDK supports the new /users endpoint, this code can be replaced so
                # that we can also update user accounts in the local db who have not sent replies.
                if isinstance(item_widget, ReplyWidget):
                    self.controller.session.refresh(conversation_item)
                    self.controller.session.refresh(conversation_item.journalist)
                    item_widget.sender = conversation_item.journalist
            else:
                # add a new item to be displayed.
                if isinstance(conversation_item, Message):
                    self.add_message(conversation_item, index)
                elif isinstance(conversation_item, (DraftReply, Reply)):
                    self.add_reply(conversation_item, conversation_item.journalist, index)
                else:
                    self.add_file(conversation_item, index)

        # If any items remain in current_conversation, they are no longer in the
        # source collection and should be removed from both the layout and the conversation
        # dict. Note that an item may be removed from the source collection if it is deleted
        # by another user (a journalist using the Web UI is able to delete individual
        # submissions).
        for item_widget in current_conversation.values():
            logger.debug("Deleting item: {}".format(item_widget.uuid))
            self.current_messages.pop(item_widget.uuid)
            item_widget.deleteLater()
            self._scroll.remove_widget_from_conversation(item_widget)

        self.update_deletion_markers()
        self.conversation_updated.emit()

    def add_file(self, file: File, index: int) -> None:
        """
        Add a file from the source.
        """
        logger.debug("Adding file for {}".format(file.uuid))
        conversation_item = FileWidget(
            file.uuid,
            self.controller,
            self.controller.file_download_started,
            self.controller.file_ready,
            self.controller.file_missing,
            index,
            self._scroll.widget().width(),
        )
        self._scroll.add_widget_to_conversation(index, conversation_item, Qt.AlignLeft)
        self.current_messages[file.uuid] = conversation_item
        self.conversation_updated.emit()

    def update_conversation_position(self, min_val: int, max_val: int) -> None:
        """
        Handler called when a new item is added to the conversation. Ensures
        it's scrolled to the bottom and thus visible.
        """
        if self.reply_flag and max_val > 0:
            self._scroll.verticalScrollBar().setValue(max_val)
            self.reply_flag = False

    def add_message(self, message: Message, index: int) -> None:
        """
        Add a message from the source.
        """
        conversation_item = MessageWidget(
            message.uuid,
            str(message),
            self.controller.message_ready,
            self.controller.message_download_failed,
            index,
            self._scroll.widget().width(),
            self.controller.authenticated_user,
            message.download_error is not None,
        )

        # Connect the on_update_authenticated_user pyqtSlot to the update_authenticated_user signal.
        self.controller.update_authenticated_user.connect(
            conversation_item.on_update_authenticated_user
        )
        # Retrieve the list of usernames of the users who have seen the message.
        conversation_item.update_seen_by_list(message.seen_by_list)
        self._scroll.add_widget_to_conversation(index, conversation_item, Qt.AlignLeft)
        self.current_messages[message.uuid] = conversation_item
        self.conversation_updated.emit()

    def add_reply(self, reply: Union[DraftReply, Reply], sender: User, index: int) -> None:
        """
        Add a reply from a journalist to the source.
        """
        try:
            send_status = reply.send_status.name
        except AttributeError:
            send_status = "SUCCEEDED"  # TODO: Add and use success status in db.ReplySendStatusCodes

        if (
            self.controller.authenticated_user
            and self.controller.authenticated_user.id == reply.journalist_id
        ):
            sender_is_current_user = True
        else:
            sender_is_current_user = False

        conversation_item = ReplyWidget(
            self.controller,
            reply.uuid,
            str(reply),
            send_status,
            self.controller.reply_ready,
            self.controller.reply_download_failed,
            self.controller.reply_succeeded,
            self.controller.reply_failed,
            index,
            self._scroll.widget().width(),
            sender,
            sender_is_current_user,
            self.controller.authenticated_user,
            failed_to_decrypt=getattr(reply, "download_error", None) is not None,
        )
        # Connect the on_update_authenticated_user pyqtSlot to the update_authenticated_user signal.
        self.controller.update_authenticated_user.connect(
            conversation_item.on_update_authenticated_user
        )
        # Retrieve the list of usernames of the users who have seen the reply.
        conversation_item.update_seen_by_list(reply.seen_by_list)
        self._scroll.add_widget_to_conversation(index, conversation_item, Qt.AlignRight)
        self.current_messages[reply.uuid] = conversation_item

    def on_reply_sent(self, source_uuid: str) -> None:
        """
        Add the reply text sent from ReplyBoxWidget to the conversation.
        """
        self.reply_flag = True
        if source_uuid == self.source.uuid:
            try:
                self.controller.session.refresh(self.source)
                self.update_conversation(self.source.collection)
            except sqlalchemy.exc.InvalidRequestError as e:
                logger.debug(e)
