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
import html
from PyQt5.QtCore import Qt, pyqtSlot
from PyQt5.QtGui import QIcon
from PyQt5.QtWidgets import QListWidget, QLabel, QWidget, QListWidgetItem, QHBoxLayout, \
    QPushButton, QVBoxLayout, QLineEdit, QScrollArea, QDialog, QAction, QMenu, \
    QMessageBox, QToolButton, QSizePolicy, QTextEdit
from uuid import uuid4

from securedrop_client.db import Source
from securedrop_client.logic import Client
from securedrop_client.resources import load_svg, load_image
from securedrop_client.storage import get_data
from securedrop_client.utils import humanize_filesize

logger = logging.getLogger(__name__)


class ToolBar(QWidget):
    """
    Represents the tool bar across the top of the user interface.
    """

    def __init__(self, parent):
        super().__init__(parent)
        layout = QHBoxLayout(self)
        self.logo = QLabel()
        self.logo.setPixmap(load_image('header_logo.png'))

        self.user_state = QLabel(_("Signed out."))

        self.login = QPushButton(_('Sign in'))
        self.login.clicked.connect(self.on_login_clicked)

        self.logout = QPushButton(_('Sign out'))
        self.logout.clicked.connect(self.on_logout_clicked)
        self.logout.setVisible(False)

        self.refresh = QPushButton(_('Refresh'))
        self.refresh.clicked.connect(self.on_refresh_clicked)
        self.refresh.setVisible(False)

        layout.addWidget(self.logo)
        layout.addStretch()
        layout.addWidget(self.user_state)
        layout.addWidget(self.login)
        layout.addWidget(self.logout)
        layout.addWidget(self.refresh)

    def setup(self, window, controller):
        """
        Store a reference to the GUI window object (through which all wider GUI
        state is controlled).

        Assign a controller object (containing the application logic) to this
        instance of the toolbar.
        """
        self.window = window
        self.controller = controller

        self.controller.sync_events.connect(self._on_sync_event)

    def set_logged_in_as(self, username):
        """
        Update the UI to reflect that the user is logged in as "username".
        """
        self.user_state.setText(_('Signed in as: ' + html.escape(username)))
        self.login.setVisible(False)
        self.logout.setVisible(True)
        self.refresh.setVisible(True)

    def set_logged_out(self):
        """
        Update the UI to a logged out state.
        """
        self.user_state.setText(_('Signed out.'))
        self.login.setVisible(True)
        self.logout.setVisible(False)
        self.refresh.setVisible(False)

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

    def on_refresh_clicked(self):
        """
        Called when the refresh button is clicked.
        """
        self.controller.sync_api()

    def _on_sync_event(self, data):
        """
        Called when the refresh call completes
        """
        self.refresh.setEnabled(data != 'syncing')


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

        self.status = QLabel(_('Waiting to refresh...'))
        self.error_status = QLabel('')
        self.error_status.setObjectName('error_label')

        left_layout.addWidget(self.status)
        left_layout.addWidget(self.error_status)

        self.source_list = SourceList(left_column)
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
        self.error_status.setText(html.escape(error))

    def set_conversation(self, widget):
        """
        Update the view holder to contain the referenced widget.
        """
        old_widget = self.view_layout.takeAt(0)

        if old_widget:
            old_widget.widget().setVisible(False)

        self.view_layout.addWidget(widget)
        widget.setVisible(True)

    def re_create_conversation_view(self):
        """Take old conversation view off, and re-create it

        The re created conversation view is blank(without any conversation).
        """
        deprecated_widget = self.layout.takeAt(1)
        if deprecated_widget:
            deprecated_widget.widget().setVisible(False)
            self.view_holder = QWidget()
            self.view_layout = QVBoxLayout()
            self.view_holder.setLayout(self.view_layout)
            self.view_holder.setVisible(True)
            self.layout.addWidget(self.view_holder, 6)


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
        current_maybe = self.currentItem() and self.itemWidget(self.currentItem())
        self.clear()

        new_current_maybe = None
        for source in sources:
            new_source = SourceWidget(self, source)
            new_source.setup(self.controller)

            list_item = QListWidgetItem(self)
            list_item.setSizeHint(new_source.sizeHint())

            self.addItem(list_item)
            self.setItemWidget(list_item, new_source)

            if current_maybe and (source.id == current_maybe.source.id):
                new_current_maybe = list_item

        if new_current_maybe:
            self.setCurrentItem(new_current_maybe)


class DeleteSourceMessageBox:
    """Use this to display operation details and confirm user choice."""

    def __init__(self, parent, source, controller):
        self.parent = parent
        self.source = source
        self.controller = controller

    def launch(self):
        """It will launch the message box.

        The Message box will warns the user regarding the severity of the
        operation. It will confirm the desire to delete the source. On positive
        answer, it will delete the record of source both from SecureDrop server
        and local state.
        """
        message = self._construct_message(self.source)
        reply = QMessageBox.question(
            self.parent,
            "",
            _(message),
            QMessageBox.Cancel | QMessageBox.Yes,
            QMessageBox.Cancel
        )

        if reply == QMessageBox.Yes:
            logger.debug("Deleting source %s" % (self.source.uuid,))
            self.controller.delete_source(self.source)

    def _construct_message(self, source):
        files = 0
        messages = 0
        for submission in source.submissions:
            if submission.filename.endswith("msg.gpg"):
                messages += 1
            else:
                files += 1

        message = (
            "<big>Deleting the Source account for",
            "<b>{}</b> will also".format(source.journalist_designation,),
            "delete {} files and {} messages.</big>".format(files, messages),
            "<br>",
            "<small>This Source will no longer be able to correspond",
            "through the log-in tied to this account.</small>",
        )
        message = ' '.join(message)
        return message


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
        self.name = QLabel()
        self.updated = QLabel()

        layout = QVBoxLayout()
        self.setLayout(layout)

        self.summary = QWidget(self)
        self.summary_layout = QHBoxLayout()
        self.summary.setLayout(self.summary_layout)

        self.attached = load_svg('paperclip.svg')
        self.attached.setMaximumSize(16, 16)

        self.summary_layout.addWidget(self.name)
        self.summary_layout.addStretch()
        self.summary_layout.addWidget(self.attached)

        layout.addWidget(self.summary)
        layout.addWidget(self.updated)

        self.delete = load_svg('cross.svg')
        self.delete.setMaximumSize(16, 16)
        self.delete.mouseReleaseEvent = self.delete_source

        self.summary_layout.addWidget(self.delete)
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
        """
        self.updated.setText(arrow.get(self.source.last_updated).humanize())
        self.display_star_icon()
        self.name.setText("<strong>{}</strong>".format(
                          html.escape(self.source.journalist_designation)))

        if self.source.document_count == 0:
            self.attached.hide()

    def toggle_star(self, event):
        """
        Called when the star is clicked.
        """
        self.controller.update_star(self.source)

    def delete_source(self, event):
        if self.controller.api is None:
            self.controller.on_action_requiring_login()
            return
        else:
            messagebox = DeleteSourceMessageBox(self, self.source, self.controller)
            messagebox.launch()


class LoginDialog(QDialog):
    """
    A dialog to display the login form.
    """

    MIN_PASSWORD_LEN = 14  # Journalist.MIN_PASSWORD_LEN on server
    MAX_PASSWORD_LEN = 128  # Journalist.MAX_PASSWORD_LEN on server
    MIN_JOURNALIST_USERNAME = 3  # Journalist.MIN_USERNAME_LEN on server

    def __init__(self, parent):
        super().__init__(parent)

    def setup(self, controller):
        self.controller = controller
        self.setMinimumSize(600, 400)
        self.setWindowTitle(_('Sign in to SecureDrop'))

        main_layout = QHBoxLayout()
        main_layout.addStretch()
        self.setLayout(main_layout)

        form = QWidget()
        layout = QVBoxLayout()
        form.setLayout(layout)

        main_layout.addWidget(form)
        main_layout.addStretch()

        self.title = QLabel(_('<h1>Sign in</h1>'))
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

        self.submit = QPushButton(_('Sign in'))
        self.submit.clicked.connect(self.validate)

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
        layout.addWidget(self.submit)
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
        self.error_label.setText(html.escape(message))

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
        tfa_token = self.tfa_field.text().replace(' ', '')
        if username and password and tfa_token:
            # Validate username
            if len(username) < self.MIN_JOURNALIST_USERNAME:
                self.setDisabled(False)
                self.error(_('Your username should be at least 3 characters. '))
                return

            # Validate password
            if len(password) < self.MIN_PASSWORD_LEN or len(password) > self.MAX_PASSWORD_LEN:
                self.setDisabled(False)
                self.error(_('Your password should be between 14 and 128 characters. '))
                return

            # Validate 2FA token
            try:
                int(tfa_token)
            except ValueError:
                self.setDisabled(False)
                self.error(_('Please use only numerals for the two factor number.'))
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

    css = "padding: 10px; min-height:20px;border: 1px solid #999; border-radius: 18px;"

    def __init__(self, message_id: str, text: str, update_signal) -> None:
        super().__init__()
        self.message_id = message_id

        layout = QVBoxLayout()
        self.setLayout(layout)

        self.message = QLabel(html.escape(text, quote=False))
        self.message.setWordWrap(True)
        self.message.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        layout.addWidget(self.message)

        update_signal.connect(self._update_text)

    @pyqtSlot(str, str)
    def _update_text(self, message_id: str, text: str) -> None:
        """
        Conditionally update this SpeechBubble's text if and only if the message_id of the emitted
        signal matches the message_id of this speech bubble.
        """
        if message_id == self.message_id:
            self.message.setText(html.escape(text, quote=False))


class ConversationWidget(QWidget):
    """
    Draws a message onto the screen.
    """

    def __init__(self,
                 message_id: str,
                 message: str,
                 update_signal,
                 align: str) -> None:
        """
        Initialise with the message to display and some notion of which side
        of the conversation ("left" or "right" [anything else]) to which the
        widget should belong.
        """
        super().__init__()
        layout = QHBoxLayout()
        label = SpeechBubble(message_id, message, update_signal)

        if align != "left":
            # Float right...
            layout.addStretch(5)
            label.setStyleSheet(label.css + 'border-bottom-right-radius: 0px;')

        layout.addWidget(label, 6)

        if align == "left":
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

    def __init__(self, message_id: str, message: str, update_signal) -> None:
        super().__init__(message_id,
                         message,
                         update_signal,
                         align="left")
        self.setStyleSheet("""
        background-color: #EEE;
        """)


class ReplyWidget(ConversationWidget):
    """
    Represents a reply to a source.
    """

    def __init__(
        self,
        message_id: str,
        message: str,
        update_signal,
        message_succeeded_signal,
        message_failed_signal,
    ) -> None:
        super().__init__(message_id,
                         message,
                         update_signal,
                         align="right")
        self.message_id = message_id
        self.setStyleSheet("""
        background-color: #2299EE;
        """)
        message_succeeded_signal.connect(self._on_reply_success)
        message_failed_signal.connect(self._on_reply_failure)

    @pyqtSlot(str)
    def _on_reply_success(self, message_id: str) -> None:
        """
        Conditionally update this ReplyWidget's state if and only if the message_id of the emitted
        signal matches the message_id of this widget.
        """
        if message_id == self.message_id:
            logger.debug('Message {} succeeded'.format(message_id))

    @pyqtSlot(str)
    def _on_reply_failure(self, message_id: str) -> None:
        """
        Conditionally update this ReplyWidget's state if and only if the message_id of the emitted
        signal matches the message_id of this widget.
        """
        if message_id == self.message_id:
            logger.debug('Message {} failed'.format(message_id))
            self.setStyleSheet("""
            background-color: #FF3E3C;
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

        if align != "left":
            # Float right...
            layout.addStretch(5)

        layout.addWidget(icon)
        layout.addWidget(description, 5)

        if align == "left":
            # Add space on right hand side...
            layout.addStretch(5)

        self.setLayout(layout)

    def mouseReleaseEvent(self, e):
        """
        Handle a completed click via the program logic. The download state
        of the file distinguishes which function in the logic layer to call.
        """
        if self.submission.is_downloaded:
            # Open the already downloaded file.
            self.controller.on_file_open(self.submission)
        else:
            # Download the file.
            self.controller.on_file_download(self.source, self.submission)


class ConversationView(QWidget):
    """
    Renders a conversation.
    """

    def __init__(self, source_db_object: Source, sdc_home: str, controller: Client, parent=None):
        super().__init__(parent)
        self.source = source_db_object
        self.sdc_home = sdc_home
        self.controller = controller
        self.setStyleSheet("background-color: #fff;")

        self.container = QWidget()
        self.conversation_layout = QVBoxLayout()
        self.container.setLayout(self.conversation_layout)
        self.container.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        self.scroll = QScrollArea()
        self.scroll.setVerticalScrollBarPolicy(Qt.ScrollBarAlwaysOn)
        self.scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.scroll.setWidget(self.container)
        self.scroll.setWidgetResizable(True)

        # Completely unintuitive way to ensure the view remains scrolled to the
        # bottom.
        sb = self.scroll.verticalScrollBar()
        sb.rangeChanged.connect(self.update_conversation_position)

        main_layout = QVBoxLayout()
        main_layout.addWidget(self.scroll)
        self.setLayout(main_layout)

        self.update_conversation(self.source.collection)

    def clear_conversation(self):
        while self.conversation_layout.count():
            child = self.conversation_layout.takeAt(0)
            if child.widget():
                child.widget().deleteLater()

    def update_conversation(self, collection: list) -> None:
        # clear all old items
        self.clear_conversation()
        # add new items
        for conversation_item in collection:
            if conversation_item.filename.endswith('msg.gpg'):
                self.add_item_content_or(self.add_message,
                                         conversation_item,
                                         "<Message not yet downloaded>")
            elif conversation_item.filename.endswith('reply.gpg'):
                self.add_item_content_or(self.add_reply,
                                         conversation_item,
                                         "<Reply not yet downloaded>")
            else:
                self.add_file(self.source, conversation_item)

    def add_item_content_or(self, adder, item, default):
        """
        Private helper function to add correct message to conversation widgets
        """
        if item.is_downloaded is False:
            adder(item.uuid, default)
        else:
            adder(item.uuid, get_data(self.sdc_home, item.filename))

    def add_file(self, source_db_object, submission_db_object):
        """
        Add a file from the source.
        """
        self.conversation_layout.addWidget(
            FileWidget(source_db_object, submission_db_object,
                       self.controller))

    def update_conversation_position(self, min_val, max_val):
        """
        Handler called when a new item is added to the conversation. Ensures
        it's scrolled to the bottom and thus visible.
        """
        current_val = self.scroll.verticalScrollBar().value()
        viewport_height = self.scroll.viewport().height()

        if current_val + viewport_height > max_val:
            self.scroll.verticalScrollBar().setValue(max_val)

    def add_message(self, message_id: str, message: str) -> None:
        """
        Add a message from the source.
        """
        self.conversation_layout.addWidget(
            MessageWidget(message_id, message, self.controller.message_sync.message_downloaded))

    def add_reply(self, message_id: str, reply: str, files=None) -> None:
        """
        Add a reply from a journalist.
        """
        self.conversation_layout.addWidget(
            ReplyWidget(message_id,
                        reply,
                        self.controller.reply_sync.reply_downloaded,
                        self.controller.reply_succeeded,
                        self.controller.reply_failed,
                        ))


class SourceConversationWrapper(QWidget):
    """
    Wrapper for a source's conversation including the chat window, profile tab, and other
    per-soruce resources.
    """

    def __init__(self, source: Source, sdc_home: str, controller: Client, parent=None) -> None:
        super().__init__(parent)
        self.source = source
        self.controller = controller
        self.layout = QVBoxLayout()
        self.setLayout(self.layout)

        self.conversation = ConversationView(self.source, sdc_home, self.controller, parent=self)
        self.source_profile = SourceProfileShortWidget(self.source, self.controller)
        self.reply_box = ReplyBoxWidget(self)

        self.layout.addWidget(self.source_profile)
        self.layout.addWidget(self.conversation)
        self.layout.addWidget(self.reply_box)

    def send_reply(self, message: str) -> None:
        msg_uuid = str(uuid4())
        self.conversation.add_reply(msg_uuid, message)
        self.controller.send_reply(self.source.uuid, msg_uuid, message)


class ReplyBoxWidget(QWidget):
    """
    A textbox where a journalist can enter a reply.
    """

    def __init__(self, conversation: SourceConversationWrapper) -> None:
        super().__init__()
        self.conversation = conversation

        self.text_edit = QTextEdit()

        self.send_button = QPushButton('Send')
        self.send_button.clicked.connect(self.send_reply)

        layout = QHBoxLayout()
        layout.addWidget(self.text_edit)
        layout.addWidget(self.send_button)
        self.setLayout(layout)

    def send_reply(self) -> None:
        msg = self.text_edit.toPlainText().strip()
        if not msg:
            return
        self.conversation.send_reply(msg)
        self.text_edit.clear()


class DeleteSourceAction(QAction):
    """Use this action to delete the source record."""

    def __init__(self, source, parent, controller):
        self.source = source
        self.controller = controller
        self.text = _("Delete source account")

        super().__init__(self.text, parent)

        self.messagebox = DeleteSourceMessageBox(
            parent, self.source, self.controller
        )
        self.triggered.connect(self.trigger)

    def trigger(self):
        if self.controller.api is None:
            self.controller.on_action_requiring_login()
            return
        else:
            self.messagebox.launch()


class SourceMenu(QMenu):
    """Renders menu having various operations.

    This menu provides below functionality via menu actions:

    1. Delete source

    Note: At present this only supports "delete" operation.
    """

    def __init__(self, source, controller):
        super().__init__()
        self.source = source
        self.controller = controller
        actions = (
            DeleteSourceAction(
                self.source,
                self,
                self.controller
            ),
        )
        for action in actions:
            self.addAction(action)


class SourceMenuButton(QToolButton):
    """An ellipse based source menu button.

    This button is responsible for launching menu on click.
    """

    def __init__(self, source, controller):
        super().__init__()
        self.controller = controller
        self.source = source

        ellipsis_icon = load_image("ellipsis.svg")
        self.setIcon(QIcon(ellipsis_icon))

        self.menu = SourceMenu(self.source, self.controller)
        self.setMenu(self.menu)

        self.setPopupMode(QToolButton.InstantPopup)


class TitleLabel(QLabel):
    """Centered aligned, HTML heading level 3 label."""

    def __init__(self, text):
        html_text = "<h3>%s</h3>" % (text,)
        super().__init__(_(html_text))
        self.setAlignment(Qt.AlignCenter)


class SourceProfileShortWidget(QWidget):
    """A widget for displaying short view for Source.

    It contains below information.
    1. Journalist designation
    2. A menu to perform various operations on Source.
    """

    def __init__(self, source, controller):
        super().__init__()
        self.source = source
        self.controller = controller

        self.layout = QHBoxLayout()
        self.setLayout(self.layout)

        widgets = (
            TitleLabel(self.source.journalist_designation),
            SourceMenuButton(self.source, self.controller),
        )

        for widget in widgets:
            self.layout.addWidget(widget)
