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

from gettext import gettext as _
from gettext import ngettext

from securedrop_client.db import Source
from securedrop_client.gui.base import ModalDialog


class DeleteSourceDialog(ModalDialog):
    """Used to confirm deletion of source accounts."""

    def __init__(self, sources: list[Source]) -> None:
        super().__init__(show_header=False, dangerous=True)
        self.sources = sources

        # If the dialog is constructed with no sources, show a warning; otherwise,
        # confirm the number and designation of the sources to be deleted
        num_sources = len(sources)
        if num_sources == 0:
            self._show_warning_nothing_selected()
        else:
            continue_text = ngettext(
                "YES, DELETE ENTIRE SOURCE ACCOUNT",
                "YES, DELETE {number} SOURCE ACCOUNTS",
                num_sources,
            ).format(number=num_sources)

            self.body.setText(self.make_body_text(self.sources))
            self.continue_button.setText(continue_text)
            self.cancel_button.setDefault(True)
            self.cancel_button.setFocus()
            self.confirmation_label.setText(_("Are you sure this is what you want?"))
            self.adjustSize()

    def make_body_text(self, sources: list[Source]) -> str:
        message_tuple = (
            "<p>",
            _("Delete entire account for: {source_or_sources}?"),
            "</p>",
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
            source_or_sources=f"<b>{self._get_source_names(sources)}</b>"
        )

    def _get_source_names(self, sources: list[Source]) -> str:
        """
        Helper. Return a comma-separated list of journalist designations.
        """
        return ", ".join([s.journalist_designation for s in sources])

    def _show_warning_nothing_selected(self) -> None:
        """
        Helper. Display warning if no sources are selected for deletion.
        Disables "Continue" button so user must close or cancel dialog.
        """
        self.continue_button.setEnabled(False)
        self.cancel_button.setFocus()
        self.cancel_button.setDefault(True)
        self.body.setText(_("No sources have been selected."))
        self.adjustSize()
