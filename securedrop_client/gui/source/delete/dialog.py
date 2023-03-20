"""
Source deletion dialog.

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
from gettext import gettext as _, ngettext
from typing import List

from securedrop_client.db import Source
from securedrop_client.gui.base import ModalDialog


class DeleteSourceDialog(ModalDialog):
    """Used to confirm deletion of source accounts."""

    def __init__(self, source: Source) -> None:
        super().__init__(show_header=False, dangerous=True)

        self.source = source

        self.body.setText(self.make_body_text())
        self.continue_button.setText(_("YES, DELETE ENTIRE SOURCE ACCOUNT"))
        self.cancel_button.setDefault(True)
        self.cancel_button.setFocus()
        self.confirmation_label.setText(_("Are you sure this is what you want?"))
        self.adjustSize()

    def make_body_text(self) -> str:
        message_tuple = (
            "<style>",
            "p {{white-space: nowrap;}}",
            "</style>",
            "<p><b>",
            _("When the entire account for a source is deleted:"),
            "</b></p>",
            "<p><b>\u2219</b>&nbsp;",
            _("The source will not be able to log in with their codename again."),
            "</p>",
            "<p><b>\u2219</b>&nbsp;",
            _("Your organization will not be able to send them replies."),
            "</p>",
            "<p><b>\u2219</b>&nbsp;",
            _("All files and messages from that source will also be destroyed."),
            "</p>",
            "<p>&nbsp;</p>",
        )

        return "".join(message_tuple).format(
            source="<b>{}</b>".format(self.source.journalist_designation)
        )


class DeleteSourcesDialog(ModalDialog):
    """Used to confirm deletion of multiple source accounts."""

    def __init__(self, sources: List[str]) -> None:
        super().__init__(show_header=False, dangerous=True)

        self.sources = sources

        self.body.setText(self.make_body_text())
        self.continue_button.setText(_("YES, DELETE ALL SOURCE ACCOUNT"))
        self.cancel_button.setDefault(True)
        self.cancel_button.setFocus()
        self.confirmation_label.setText(_("Are you sure this is what you want?"))
        self.adjustSize()

    def make_body_text(self) -> str:
        num_sources = len(self.sources)
        message_tuple = (
            "<style>",
            "p {{white-space: nowrap;}}",
            "</style>",
            "<p><b>",
            ngettext(
                "You are about to delete 1 source account",
                f"You are about to delete {num_sources} accounts",
                num_sources,
            ),
            "</b></p>",
            "<p><b>",
            _("When the entire account for all source are deleted:"),
            "</b></p>",
            "<p><b>\u2219</b>&nbsp;",
            _("The sources will not be able to log in with their codename again."),
            "</p>",
            "<p><b>\u2219</b>&nbsp;",
            _("Your organization will not be able to send them replies."),
            "</p>",
            "<p><b>\u2219</b>&nbsp;",
            _("All files and messages from the sources will also be destroyed."),
            "</p>",
            "<p>&nbsp;</p>",
        )

        return "".join(message_tuple)
