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
import arrow
from PyQt5.QtCore import Qt
from PyQt5.QtGui import QPainter
from PyQt5.QtWidgets import (QListWidget, QTextEdit, QLabel, QToolBar, QAction,
                             QWidget, QListWidgetItem, QHBoxLayout,
                             QPushButton, QVBoxLayout, QLineEdit, QScrollArea,
                             QPlainTextEdit, QSpacerItem, QSizePolicy, QDialog)
from securedrop_client.resources import load_svg, load_image
from securedrop_client.utils import humanize_filesize


logger = logging.getLogger(__name__)


class ToolBar(QWidget):
    """
    Represents the tool bar across the top of the user interface.

    ToDo: this is a work in progress and will be updated soon.
    """

    def __init__(self, parent):
        super().__init__(parent)
        layout = QHBoxLayout(self)
        self.logo = QLabel()
        self.logo.setPixmap(load_image('header_logo.png'))
        self.user_state = QLabel(_("Logged out."))
        self.login = QPushButton(_('Sign In'))
        self.login.clicked.connect(self.on_login_clicked)
        self.logout = QPushButton(_('Log Out'))
        self.logout.clicked.connect(self.on_logout_clicked)
        self.logout.setVisible(False)
        layout.addWidget(self.logo)
        layout.addStretch()
        layout.addWidget(self.user_state)
        layout.addWidget(self.login)
        layout.addWidget(self.logout)

    def setup(self, window, controller):
        """
        Store a reference to the GUI window object (through which all wider GUI
        state is controlled).

        Assign a controller object (containing the application logic) to this
        instance of the toolbar.
        """
        self.window = window
        self.controller = controller

    def set_logged_in_as(self, username):
        """
        Update the UI to reflect that the user is logged in as "username".
        """
        self.user_state.setText(_('Logged in as: ' + username))
        self.login.setVisible(False)
        self.logout.setVisible(True)

    def set_logged_out(self):
        """
        Update the UI to a logged out state.
        """
        self.user_state.setText(_('Logged out.'))
        self.login.setVisible(True)
        self.logout.setVisible(False)

    def on_login_clicked(self):
        """
        Called when the login button is clicked.
        """
        self.window.show_login()

    def on_logout_clicked(self):
        """
        Called when the logout button is clicked.
        """
        self.controller.logout()


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
        self.status = QLabel(_('Waiting to Synchronize'))
        self.error_status = QLabel('')
        self.error_status.setObjectName('error_label')
        left_layout.addWidget(self.status)
        left_layout.addWidget(self.error_status)
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
        self.view_layout = QVBoxLayout()
        self.view_holder.setLayout(self.view_layout)
        self.layout.addWidget(self.view_holder, 6)

    def setup(self, controller):
        """
        Pass through the controller object to this widget.
        """
        self.controller = controller
        self.source_list.setup(controller)

    def update_error_status(self, error=None):
        self.error_status.setText(error)

    def update_view(self, widget):
        """
        Update the view holder to contain the referenced widget.
        """
        old_widget = self.view_layout.takeAt(0)
        if old_widget:
            old_widget.widget().setVisible(False)
        widget.setVisible(True)
        self.view_layout.addWidget(widget)


class SourceList(QListWidget):
    """
    Displays the list of sources.
    """

    def __init__(self, parent):
        super().__init__(parent)

    def setup(self, controller):
        """
        Pass through the controller object to this widget.
        """
        self.controller = controller

    def update(self, sources):
        """
        Reset and update the list with the passed in list of sources.
        """
        self.clear()
        for source in sources:
            new_source = SourceWidget(self, source)
            new_source.setup(self.controller)
            list_item = QListWidgetItem(self)
            list_item.setSizeHint(new_source.sizeHint())
            self.addItem(list_item)
            self.setItemWidget(list_item, new_source)


class SourceWidget(QWidget):
    """
    Used to display summary information about a source in the list view.
    """

    def __init__(self, parent, source):
        """
        Set up the child widgets.
        """
        super().__init__(parent)
        self.source = source
        layout = QVBoxLayout()
        self.setLayout(layout)
        self.summary = QWidget(self)
        self.summary_layout = QHBoxLayout()
        self.summary.setLayout(self.summary_layout)
        self.attached = load_svg('paperclip.svg')
        self.attached.setMaximumSize(16, 16)
        self.name = QLabel()
        self.summary_layout.addWidget(self.name)
        self.summary_layout.addStretch()
        self.summary_layout.addWidget(self.attached)
        layout.addWidget(self.summary)
        self.updated = QLabel()
        layout.addWidget(self.updated)
        self.details = QLabel()
        self.details.setWordWrap(True)
        layout.addWidget(self.details)
        self.update()

    def setup(self, controller):
        """
        Pass through the controller object to this widget.
        """
        self.controller = controller

    def display_star_icon(self):
        """
        Show the correct star icon
        """
        if getattr(self, 'starred', None):  # Delete icon if it exists.
            self.summary_layout.removeWidget(self.starred)

        if self.source.is_starred:
            self.starred = load_svg('star_on.svg')
        else:
            self.starred = load_svg('star_off.svg')

        self.summary_layout.addWidget(self.starred)
        self.starred.setMaximumSize(16, 16)
        self.starred.mousePressEvent = self.toggle_star

    def update(self):
        """
        Updates the displayed values with the current values from self.source.

        TODO: Style this widget properly and work out what should be in the
        self.details label.
        """
        self.updated.setText(arrow.get(self.source.last_updated).humanize())
        self.display_star_icon()
        self.name.setText("<strong>{}</strong>".format(
                          self.source.journalist_designation))
        self.details.setText("Lorum ipsum dolor sit amet thingy dodah...")

    def toggle_star(self, event):
        """
        Called when the star is clicked.
        """
        self.controller.update_star(self.source)


class LoginDialog(QDialog):
    """
    A dialog to display the login form.
    """

    def __init__(self, parent):
        super().__init__(parent)

    def setup(self, controller):
        self.controller = controller
        self.setMinimumSize(600, 400)
        self.setWindowTitle(_('Login to SecureDrop'))
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
        self.submit.clicked.connect(self.validate)
        gutter_layout.addWidget(self.help_url)
        gutter_layout.addWidget(self.submit)
        self.error_label = QLabel('')
        self.error_label.setObjectName('error_label')
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
        layout.addWidget(self.error_label)
        layout.addStretch()

    def reset(self):
        """
        Resets the login form to the default state.
        """
        self.username_field.setText('')
        self.username_field.setFocus()
        self.password_field.setText('')
        self.tfa_field.setText('')
        self.setDisabled(False)
        self.error_label.setText('')

    def error(self, message):
        """
        Ensures the passed in message is displayed as an error message.
        """
        self.setDisabled(False)
        self.error_label.setText(message)

    def validate(self):
        """
        Validate the user input -- we expect values for:

        * username (free text)
        * password (free text)
        * TFA token (numerals)
        """
        self.setDisabled(True)
        username = self.username_field.text()
        password = self.password_field.text()
        tfa_token = self.tfa_field.text()
        if username and password and tfa_token:
            try:
                int(tfa_token)
            except ValueError:
                self.setDisabled(False)
                self.error(_('Please use only numerals (no spaces) for the '
                             'two factor number.'))
                return
            self.controller.login(username, password, tfa_token)
        else:
            self.setDisabled(False)
            self.error(_('Please enter a username, password and '
                         'two factor number.'))


class SpeechBubble(QWidget):
    """
    Represents a speech bubble that's part of a conversation between a source
    and journalist.
    """

    css = "padding: 10px; border: 1px solid #999; border-radius: 20px;"

    def __init__(self, text):
        super().__init__()
        layout = QVBoxLayout()
        self.setLayout(layout)
        message = QLabel(text)
        message.setWordWrap(True)
        layout.addWidget(message)


class ConversationWidget(QWidget):
    """
    Draws a message onto the screen.
    """

    def __init__(self, message, align):
        """
        Initialise with the message to display and some notion of which side
        of the conversation ("left" or "right" [anything else]) to which the
        widget should belong.
        """
        super().__init__()
        layout = QHBoxLayout()
        label = SpeechBubble(message)
        if align is not "left":
            # Float right...
            layout.addStretch(5)
            label.setStyleSheet(label.css + 'border-bottom-right-radius: 0px;')
        layout.addWidget(label, 6)
        if align is "left":
            # Add space on right hand side...
            layout.addStretch(5)
            label.setStyleSheet(label.css + 'border-bottom-left-radius: 0px;')
        layout.setContentsMargins(0, 0, 0, 0)
        self.setLayout(layout)
        self.setContentsMargins(0, 0, 0, 0)


class MessageWidget(ConversationWidget):
    """
    Represents an incoming message from the source.
    """

    def __init__(self, message):
        super().__init__(message, align="left")
        self.setStyleSheet("""
        background-color: #EEE;
        """)


class ReplyWidget(ConversationWidget):
    """
    Represents a reply to a source.
    """

    def __init__(self, message):
        super().__init__(message, align="right")
        self.setStyleSheet("""
        background-color: #2299EE;
        """)


class FileWidget(QWidget):
    """
    Represents a file.
    """

    def __init__(self, source_db_object, submission_db_object,
                 controller, align="left"):
        """
        Given some text, an indication of alignment ('left' or 'right') and
        a reference to the controller, make something to display a file.

        Align is set to left by default because currently SecureDrop can only
        accept files from sources to journalists.
        """
        super().__init__()
        self.controller = controller
        self.source = source_db_object
        self.submission = submission_db_object
        layout = QHBoxLayout()
        icon = QLabel()
        icon.setPixmap(load_image('file.png'))
        if submission_db_object.is_downloaded:
            description = QLabel("Open")
        else:
            human_filesize = humanize_filesize(self.submission.size)
            description = QLabel("Download ({})".format(human_filesize))
        if align is not "left":
            # Float right...
            layout.addStretch(5)
        layout.addWidget(icon)
        layout.addWidget(description, 5)
        if align is "left":
            # Add space on right hand side...
            layout.addStretch(5)
        self.setLayout(layout)

    def mouseDoubleClickEvent(self, e):
        """
        Handle a double-click via the program logic.
        """
        self.controller.on_file_click(self.source, self.submission)


class ConversationView(QWidget):
    """
    Renders a conversation.
    """

    def __init__(self, parent):
        super().__init__(parent)
        self.container = QWidget()
        self.conversation_layout = QVBoxLayout()
        self.container.setLayout(self.conversation_layout)
        self.container.setStyleSheet("background-color: #fff;")

        self.scroll = QScrollArea()
        self.scroll.setVerticalScrollBarPolicy(Qt.ScrollBarAlwaysOn)
        self.scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.scroll.setWidget(self.container)
        self.scroll.setWidgetResizable(True)
        # Completely unintuitive way to ensure the view remains scrolled to the
        # bottom.
        sb = self.scroll.verticalScrollBar()
        sb.rangeChanged.connect(self.move_to_bottom)

        main_layout = QVBoxLayout()
        main_layout.addWidget(self.scroll)
        self.setLayout(main_layout)

    def setup(self, controller):
        """
        Ensure there's a reference to program logic.
        """
        self.controller = controller

    def add_file(self, source_db_object, submission_db_object):
        """
        Add a file from the source.
        """
        self.conversation_layout.addWidget(
            FileWidget(source_db_object, submission_db_object,
                       self.controller))

    def move_to_bottom(self, min_val, max_val):
        """
        Handler called when a new item is added to the conversation. Ensures
        it's scrolled to the bottom and thus visible.
        """
        self.scroll.verticalScrollBar().setValue(max_val)

    def add_message(self, message):
        """
        Add a message from the source.
        """
        self.conversation_layout.addWidget(MessageWidget(message))

    def add_reply(self, reply, files=None):
        """
        Add a reply from a journalist.
        """
        self.conversation_layout.addWidget(ReplyWidget(reply))
