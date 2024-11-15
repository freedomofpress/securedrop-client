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

from PyQt5.QtCore import QTimer

from securedrop_client.db import Source
from securedrop_client.gui.base import ModalDialog

# Maximum number of source names to display in delete dialog before
# (a) truncation of the list and (b) delayed confirmation:
LOTS_OF_SOURCES = 30

# Timers for delayed confirmation:
SEC = 1000  # ms
CONTINUE_BUTTON_DELAY = 5 * SEC


class DeleteSourceDialog(ModalDialog):
    """Used to confirm deletion of source accounts."""

    def __init__(self, sources: list[Source], source_total: int) -> None:
        super().__init__(show_header=False, dangerous=True)
        self.sources = sources
        self.source_total = source_total
        self.continue_text = "CONTINUE"

        # If the dialog is constructed with no sources, show a warning; otherwise,
        # confirm the number and designation of the sources to be deleted
        num_sources = len(sources)
        if num_sources == 0:
            self._show_warning_nothing_selected()
        else:
            if num_sources < source_total:
                self.continue_text = ngettext(
                    "YES, DELETE ENTIRE SOURCE ACCOUNT",
                    "YES, DELETE {number} SOURCE ACCOUNTS",
                    num_sources,
                ).format(number=num_sources)
            else:
                self.continue_text = ngettext(
                    "YES, DELETE ENTIRE SOURCE ACCOUNT",  # in this case, all 1 accounts.
                    "YES, DELETE ALL {number} SOURCE ACCOUNTS",
                    num_sources,
                ).format(number=num_sources)

            self.body.setText(self.make_body_text(self.sources, self.source_total))
            self.continue_button.setText(self.continue_text)
            self.cancel_button.setDefault(True)
            self.cancel_button.setFocus()
            self.confirmation_label.setText(_("Are you sure this is what you want?"))
            self.adjustSize()

            if num_sources > LOTS_OF_SOURCES:
                self.block_continue_button()

    def block_continue_button(self) -> None:
        """Disable the `continue_button` until `CONTINUE_BUTTON_DELAY` has elapsed."""
        self.continue_button_delay = CONTINUE_BUTTON_DELAY
        self.continue_button_timer = QTimer(self)
        self.continue_button_timer.setInterval(SEC)
        self.continue_button_timer.timeout.connect(self.update_continue_button)

        self.update_continue_button(True)
        self.continue_button_timer.start()

    def update_continue_button(self, initial: bool = False) -> None:
        """
        Update the `continue_button` either initially (disabled) or based on
        `CONTINUE_BUTTON_DELAY` remaining.
        """
        # Zeroth tick doesn't count.
        if not initial:
            self.continue_button_delay -= self.continue_button_timer.interval()

        # Keep the button disabled and the label updated with the delay remaining...
        if self.continue_button_delay > 0:
            self.continue_button.setDisabled(True)
            self.continue_button.setText(
                _("{text} (wait {delay} sec)").format(
                    text=self.continue_text, delay=int(self.continue_button_delay / SEC)
                )
            )
        # ...until the delay has elapsed: then reenable the button with its original label.
        else:
            self.continue_button_timer.stop()
            self.continue_button.setText(self.continue_text)
            self.continue_button.setEnabled(True)

    def make_body_text(self, sources: list[Source], source_total: int) -> str:
        if len(sources) == source_total:
            all_sources_text = ("<p><b>", _("Notice: All sources have been selected!"), "</p></b>")
        else:
            all_sources_text = ("", "", "")

        message_text = (
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

        full_text = all_sources_text + message_text
        return "".join(full_text).format(
            source_or_sources=f"<b>{self._get_source_names_truncated(sources, LOTS_OF_SOURCES)}</b>"
        )

    def _get_source_names_truncated(self, sources: list[Source], max_shown: int) -> str:
        """
        Helper. Return a comma-separated list of journalist designations, truncated to avoid
        text overflows. If the limit is N and there are N+2 sources, all N+2 are displayed.
        If there are >N+2 sources, N sources and an additional message (approx 2 source names
        long) is displayed.
        """
        if len(sources) <= max_shown + 2:
            return self._get_source_names(sources)
        else:
            shortlist = sources[:max_shown]
            return _("{sources} ... plus {count} additional sources").format(
                sources=", ".join([s.journalist_designation for s in shortlist]),
                count=len(sources) - max_shown,
            )

    def _get_source_names(self, sources: list[Source]) -> str:
        """
        Helper. Return a comma-separated list of journalist designations.
        """
        return ", ".join([s.journalist_designation for s in sources])

    def _show_warning_nothing_selected(self) -> None:
        """
        Helper. Display warning if no sources are selected for deletion.
        Hides "Continue" button so user must close or cancel dialog.
        """
        self.continue_button.setEnabled(False)
        self.continue_button.setVisible(False)
        self.cancel_button.setFocus()
        self.cancel_button.setDefault(True)
        self.body.setText(_("No sources have been selected."))
        self.adjustSize()
