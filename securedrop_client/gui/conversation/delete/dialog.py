"""
Conversation deletion dialog.

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
from gettext import gettext as _
from gettext import ngettext

from securedrop_client.db import File, Message, Reply, Source
from securedrop_client.gui.base import ModalDialog


class DeleteConversationDialog(ModalDialog):
    """
    Shown to confirm deletion of all content in a source conversation.
    """

    def __init__(self, source: Source) -> None:
        super().__init__(show_header=False, dangerous=False)

        self.source = source

        self.body.setText(self.make_body_text())

        self.continue_button.setText(_("YES, DELETE FILES AND MESSAGES"))
        self.continue_button.setFocus()

        self.adjustSize()

    def make_body_text(self) -> str:
        files = 0
        messages = 0
        replies = 0
        for submission in self.source.collection:
            if isinstance(submission, Message):
                messages += 1
            if isinstance(submission, Reply):
                replies += 1
            elif isinstance(submission, File):
                files += 1

        message_tuple = (
            "<style>li {{line-height: 150%;}}</li></style>",
            "<p>",
            _(
                "You would like to delete {files_to_delete}, {replies_to_delete}, "
                "{messages_to_delete} from the source account for {source}?"
            ),
            "</p>",
            "<p>",
            _(
                "Preserving the account will retain its metadata, and the ability for {source} "
                "to log in to your SecureDrop again."
            ),
            "</p>",
        )

        files_to_delete = ngettext("one file", "{file_count} files", files).format(file_count=files)

        replies_to_delete = ngettext("one reply", "{reply_count} replies", replies).format(
            reply_count=replies
        )

        messages_to_delete = ngettext("one message", "{message_count} messages", messages).format(
            message_count=messages
        )

        source = "<b>{}</b>".format(self.source.journalist_designation)

        return "".join(message_tuple).format(
            files_to_delete=files_to_delete,
            messages_to_delete=messages_to_delete,
            replies_to_delete=replies_to_delete,
            source=source,
        )
