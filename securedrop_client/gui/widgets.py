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
import logging
from PyQt5.QtCore import Qt
from PyQt5.QtWidgets import (QListWidget, QTextEdit, QLabel, QToolBar, QAction,
                             QWidget, QListWidgetItem, QHBoxLayout,
                             QPushButton, QVBoxLayout, QLineEdit,
                             QPlainTextEdit)
from securedrop_client.resources import load_svg


logger = logging.getLogger(__name__)


class ToolBar(QWidget):
    """
    Represents the tool bar across the top of the user interface.
    """

    def __init__(self, parent):
        super().__init__(parent)
        self.setMaximumHeight(48)
        layout = QHBoxLayout(self)
        self.status = QLabel(_("Synchronized: 5 minutes ago."))
        self.user_state = QLabel(_("Logged in as: Testy McTestface"))
        layout.addWidget(self.status)
        layout.addStretch()
        layout.addWidget(self.user_state)


class MainView(QWidget):
    """
    Represents the main content of the application (containing the source list
    and main context view).
    """

    def __init__(self, parent):
        super().__init__(parent)
        self.layout = QHBoxLayout(self)
        self.setLayout(self.layout)
        left_column = QWidget(parent=self)
        left_layout = QVBoxLayout()
        left_column.setLayout(left_layout)
        filter_widget = QWidget()
        filter_layout = QHBoxLayout()
        filter_widget.setLayout(filter_layout)
        filter_label = QLabel(_('Filter: '))
        self.filter_term = QLineEdit()
        self.source_list = SourceList(left_column)
        filter_layout.addWidget(filter_label)
        filter_layout.addWidget(self.filter_term)
        left_layout.addWidget(filter_widget)
        left_layout.addWidget(self.source_list)
        self.layout.addWidget(left_column, 2)
        self.view_holder = QWidget()
        self.layout.addWidget(self.view_holder, 6)

    def update_view(self, widget):
        """
        Update the view holder to contain the referenced widget.
        """
        layout = QVBoxLayout()
        self.view_holder.setLayout(layout)
        layout.addWidget(widget)


class SourceList(QListWidget):
    """
    Represents the list of sources.
    """

    def update(self, sources):
        """
        Reset and update the list with the passed in list of sources.
        """
        self.clear()
        for source in sources:
            new_source = SourceWidget(source, self)
            list_item = QListWidgetItem(self)
            list_item.setSizeHint(new_source.sizeHint())
            self.addItem(list_item)
            self.setItemWidget(list_item, new_source)


class SourceWidget(QWidget):
    """
    Used to display summary information about a source in the list view.
    """

    def __init__(self, source, parent):
        """
        Set up the child widgets.
        """
        super().__init__(parent)
        self.source = source
        layout = QVBoxLayout()
        self.setLayout(layout)
        self.summary = QWidget(self)
        summary_layout = QHBoxLayout()
        self.summary.setLayout(summary_layout)
        self.updated = QLabel()
        self.attached = load_svg('paperclip.svg')
        self.attached.setMaximumSize(16, 16)
        self.starred = load_svg('star_on.svg')
        self.starred.setMaximumSize(16, 16)
        summary_layout.addWidget(self.updated)
        summary_layout.addStretch()
        summary_layout.addWidget(self.attached)
        summary_layout.addWidget(self.starred)
        layout.addWidget(self.summary)
        self.name = QLabel()
        layout.addWidget(self.name)
        self.details = QLabel()
        self.details.setWordWrap(True)
        layout.addWidget(self.details)
        self.update()

    def update(self):
        """
        Updates the displayed values with the current values from self.source.
        """
        self.updated.setText("5 minutes ago")  # str(self.source.last_updated))
        """
        if self.source.is_starred:
            self.starred.setText("[*]")
        else:
            self.starred.setText("[ ]")
        """
        self.name.setText(self.source)  # self.source.journalist_designation)
        self.details.setText("Lorum ipsum dolor sit amet thingy dodah...")


class LoginView(QWidget):
    """
    A widget to display the login form.
    """

    def __init__(self, parent):
        super().__init__(parent)
        main_layout = QHBoxLayout()
        main_layout.addStretch()
        self.setLayout(main_layout)
        form = QWidget()
        layout = QVBoxLayout()
        form.setLayout(layout)
        main_layout.addWidget(form)
        main_layout.addStretch()
        self.title = QLabel(_('<h1>Sign In</h1>'))
        self.title.setTextFormat(Qt.RichText)
        self.instructions = QLabel(_('You may read all documents and messages '
                                     'shown here, without signing in. To '
                                     'correspond with a Source or to check '
                                     'the server for updates, you must sign '
                                     'in.'))
        self.instructions.setWordWrap(True)
        self.username_label = QLabel(_('Username'))
        self.username_field = QLineEdit()
        self.password_label = QLabel(_('Password'))
        self.password_field = QLineEdit()
        self.password_field.setEchoMode(QLineEdit.Password)
        self.tfa_label = QLabel(_('Two-Factor Number'))
        self.tfa_field = QLineEdit()
        self.tfa_field.setEchoMode(QLineEdit.Password)
        gutter = QWidget(self)
        gutter_layout = QHBoxLayout()
        gutter.setLayout(gutter_layout)
        self.help_url = QLabel(_('<a href="#">Trouble Signing In?</a>'))
        self.help_url.setTextFormat(Qt.RichText)
        self.help_url.setOpenExternalLinks(True)
        self.submit = QPushButton(_('Sign In'))
        gutter_layout.addWidget(self.help_url)
        gutter_layout.addWidget(self.submit)
        layout.addStretch()
        layout.addWidget(self.title)
        layout.addWidget(self.instructions)
        layout.addWidget(self.username_label)
        layout.addWidget(self.username_field)
        layout.addWidget(self.password_label)
        layout.addWidget(self.password_field)
        layout.addWidget(self.tfa_label)
        layout.addWidget(self.tfa_field)
        layout.addWidget(gutter)
        layout.addStretch()
