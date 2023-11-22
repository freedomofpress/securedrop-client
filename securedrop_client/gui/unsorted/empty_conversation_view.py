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
from gettext import gettext as _

from PyQt5.QtCore import Qt
from PyQt5.QtWidgets import QHBoxLayout, QLabel, QVBoxLayout, QWidget

logger = logging.getLogger(__name__)


class EmptyConversationView(QWidget):
    MARGIN = 30
    NEWLINE_HEIGHT_PX = 35

    def __init__(self) -> None:
        super().__init__()

        self.setObjectName("EmptyConversationView")

        # Set layout
        layout = QHBoxLayout()
        layout.setContentsMargins(self.MARGIN, self.MARGIN, self.MARGIN, self.MARGIN)
        self.setLayout(layout)

        # Create widgets
        self.no_sources = QWidget()
        self.no_sources.setObjectName("EmptyConversationView_no_sources")
        no_sources_layout = QVBoxLayout()
        self.no_sources.setLayout(no_sources_layout)
        no_sources_instructions = QLabel(_("Nothing to see just yet!"))
        no_sources_instructions.setObjectName("EmptyConversationView_instructions")
        no_sources_instructions.setWordWrap(True)
        no_sources_instruction_details1 = QLabel(
            _("Source submissions will be listed to the left, once downloaded and decrypted.")
        )
        no_sources_instruction_details1.setWordWrap(True)
        no_sources_instruction_details2 = QLabel(
            _("This is where you will read messages, reply to sources, and work with files.")
        )
        no_sources_instruction_details2.setWordWrap(True)
        no_sources_layout.addWidget(no_sources_instructions)
        no_sources_layout.addSpacing(self.NEWLINE_HEIGHT_PX)
        no_sources_layout.addWidget(no_sources_instruction_details1)
        no_sources_layout.addSpacing(self.NEWLINE_HEIGHT_PX)
        no_sources_layout.addWidget(no_sources_instruction_details2)

        self.no_source_selected = QWidget()
        self.no_source_selected.setObjectName("EmptyConversationView_no_source_selected")
        no_source_selected_layout = QVBoxLayout()
        self.no_source_selected.setLayout(no_source_selected_layout)
        no_source_selected_instructions = QLabel(_("Select a source from the list, to:"))
        no_source_selected_instructions.setObjectName("EmptyConversationView_instructions")
        no_source_selected_instructions.setWordWrap(True)
        bullet1 = QWidget()
        bullet1_layout = QHBoxLayout()
        bullet1_layout.setContentsMargins(0, 0, 0, 0)
        bullet1.setLayout(bullet1_layout)
        bullet1_bullet = QLabel("·")  # nosemgrep: semgrep.untranslated-gui-string
        bullet1_bullet.setObjectName("EmptyConversationView_bullet")
        bullet1_layout.addWidget(bullet1_bullet)
        bullet1_layout.addWidget(QLabel(_("Read a conversation")))
        bullet1_layout.addStretch()
        bullet2 = QWidget()
        bullet2_layout = QHBoxLayout()
        bullet2_layout.setContentsMargins(0, 0, 0, 0)
        bullet2.setLayout(bullet2_layout)
        bullet2_bullet = QLabel("·")  # nosemgrep: semgrep.untranslated-gui-string
        bullet2_bullet.setObjectName("EmptyConversationView_bullet")
        bullet2_layout.addWidget(bullet2_bullet)
        bullet2_layout.addWidget(QLabel(_("View or retrieve files")))
        bullet2_layout.addStretch()
        bullet3 = QWidget()
        bullet3_layout = QHBoxLayout()
        bullet3_layout.setContentsMargins(0, 0, 0, 0)
        bullet3.setLayout(bullet3_layout)
        bullet3_bullet = QLabel("·")  # nosemgrep: semgrep.untranslated-gui-string
        bullet3_bullet.setObjectName("EmptyConversationView_bullet")
        bullet3_layout.addWidget(bullet3_bullet)
        bullet3_layout.addWidget(QLabel(_("Send a response")))
        bullet3_layout.addStretch()
        no_source_selected_layout.addWidget(no_source_selected_instructions)
        no_source_selected_layout.addSpacing(self.NEWLINE_HEIGHT_PX)
        no_source_selected_layout.addWidget(bullet1)
        no_source_selected_layout.addWidget(bullet2)
        no_source_selected_layout.addWidget(bullet3)
        no_source_selected_layout.addSpacing(self.NEWLINE_HEIGHT_PX * 4)

        # Add widgets
        layout.addWidget(self.no_sources, alignment=Qt.AlignCenter)
        layout.addWidget(self.no_source_selected, alignment=Qt.AlignCenter)

    def show_no_sources_message(self) -> None:
        self.no_sources.show()
        self.no_source_selected.hide()

    def show_no_source_selected_message(self) -> None:
        self.no_sources.hide()
        self.no_source_selected.show()
