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
from PyQt5.QtCore import Qt, pyqtSlot, QTimer
from PyQt5.QtGui import QIcon, QPalette, QBrush, QColor, QFont, QLinearGradient
from PyQt5.QtWidgets import QListWidget, QLabel, QWidget, QListWidgetItem, QHBoxLayout, \
    QPushButton, QVBoxLayout, QLineEdit, QScrollArea, QDialog, QAction, QMenu, QMessageBox, \
    QToolButton, QSizePolicy, QTextEdit, QStatusBar, QGraphicsDropShadowEffect
from typing import List
from uuid import uuid4

from securedrop_client.db import Source, Message, File
from securedrop_client.logic import Client
from securedrop_client.resources import load_svg, load_icon, load_image, load_icon_button
from securedrop_client.utils import humanize_filesize

logger = logging.getLogger(__name__)


class TopPane(QWidget):
    """
    Top pane of the app window.
    """

    def __init__(self):
        super().__init__()
        self.setStyleSheet('''
        QStatusBar::item { border: none; }
        QPushButton { border: none; color: #fff }
        QStatusBar#activity_status_bar { color: #fff; }
        QWidget#error_bar { background-color: #f22b5d }
        QPushButton#error_icon {
            background-color: qlineargradient( x1: 0, y1: 0, x2: 0, y2: 1, stop: 0 #fff, \
            stop: 0.2 #efeef7, stop: 1 #dce4ee);
        }
        QStatusBar#error_status_bar {
            color: #f22b5d;
            font-weight: bold;
            background-color: qlineargradient( x1: 0, y1: 0, x2: 0, y2: 1, \
            stop: 0 #fff, stop: 0.2 #efeef7, stop: 1 #dce4ee);
        }
        ''')
        palette = QPalette()
        gradient = QLinearGradient(0, 0, 900, 0)
        gradient.setColorAt(0, QColor('#0565d4'))
        gradient.setColorAt(1, QColor('#002c55'))
        palette.setBrush(QPalette.Background, QBrush(gradient))
        self.setPalette(palette)
        self.setAutoFillBackground(True)
        self.setFixedHeight(42)

        layout = QHBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Create refresh button
        self.refresh = load_icon_button(normal='refresh.svg', disabled='refresh_offline.svg')
        self.refresh.clicked.connect(self.on_refresh_clicked)
        self.refresh.setFixedWidth(42)
        self.refresh.setEnabled(False)

        # Create activity status bar
        self.activity_status_bar = QStatusBar()
        self.activity_status_bar.setObjectName('activity_status_bar')
        self.activity_status_bar.setSizeGripEnabled(False)

        # Add vertical error bar
        self.error_bar = QWidget()
        self.error_bar.setObjectName('error_bar')
        self.error_bar.setFixedSize(10, 42)
        self.error_bar.hide()

        # Add error icon
        self.error_icon = load_icon_button('error_icon.svg')
        self.error_icon.setObjectName('error_icon')
        self.error_icon.setFixedSize(42, 42)
        self.error_icon.hide()

        # Add error status bar
        self.error_status_bar = QStatusBar()
        self.error_status_bar.setObjectName('error_status_bar')
        self.error_status_bar.setSizeGripEnabled(False)
        self.error_status_bar.hide()

        # Add space the size of the status bar to keep the error status bar centered
        spacer = QWidget()
        spacer.setObjectName('spacer')

        # Add space ths size of the refresh icon to keep the error status bar centered
        spacer2 = QWidget()
        spacer2.setObjectName('spacer')
        spacer2.setFixedWidth(42)

        # Set height of top pane to 42 pixels
        self.refresh.setFixedHeight(42)
        self.activity_status_bar.setFixedHeight(42)
        self.error_status_bar.setFixedHeight(42)
        spacer.setFixedHeight(42)
        spacer2.setFixedHeight(42)

        # Add widgets to layout
        layout.addWidget(self.refresh, 1)
        layout.addWidget(self.activity_status_bar, 1)
        layout.addWidget(self.error_bar, 1)
        layout.addWidget(self.error_icon, 1)
        layout.addWidget(self.error_status_bar, 3)
        layout.addWidget(spacer, 1)
        layout.addWidget(spacer2)

        # Only show errors for a set duration
        self.error_status_timer = QTimer()
        self.error_status_timer.timeout.connect(self._on_error_status_timeout_event)

    def setup(self, controller):
        """
        Assign a controller object (containing the application logic).
        """
        self.controller = controller
        self.controller.sync_events.connect(self._on_sync_event)

    def on_refresh_clicked(self):
        """
        Called when the refresh button is clicked.
        """
        self.controller.sync_api()
        # Using `addPixmap` with the option `QIcon.Active` to set the icon's active state image
        # doesn't work as expected so this is a temporary solution to show that the icon was
        # clicked. The icon image is later replaced in _on_sync_event when the refresh call
        # completes.
        self.refresh.setIcon(load_icon('refresh_active.svg'))

    def enable_refresh(self):
        """
        Enable the refresh button.
        """
        self.refresh.setEnabled(True)

    def disable_refresh(self):
        """
        Disable the refresh button.
        """
        self.refresh.setEnabled(False)

    def _on_sync_event(self, data):
        """
        Called when the refresh call completes
        """
        self.refresh.setIcon(load_icon('refresh.svg'))

    def _on_error_status_timeout_event(self):
        self.error_bar.hide()
        self.error_icon.hide()
        self.error_status_bar.hide()

    def update_activity_status(self, message: str, duration: int):
        """
        Display an activity status message to the user. Optionally, supply a duration
        (in milliseconds), the default will continuously show the message.
        """
        self.activity_status_bar.showMessage(message, duration)

    def update_error_status(self, message: str, duration: int):
        """
        Display an activity status message to the user. Optionally, supply a duration
        (in milliseconds), the default will continuously show the message.
        """
        self.error_status_bar.showMessage(message, duration)
        self.error_status_timer.start(duration)
        self.error_bar.show()
        self.error_icon.show()
        self.error_status_bar.show()

    def clear_error_status(self):
        """
        Clear any message currently in the error status bar.
        """
        self.error_status_bar.clearMessage()


class ToolBar(QWidget):
    """
    Represents the tool bar across the top of the user interface.
    """

    def __init__(self, parent: QWidget):
        super().__init__(parent)

        layout = QVBoxLayout(self)
        layout.setContentsMargins(20, 10, 20, 10)
        palette = QPalette()
        gradient = QLinearGradient(0, 0, 0, 700)
        gradient.setColorAt(0, QColor('#0093da'))
        gradient.setColorAt(1, QColor('#0c3e75'))
        palette.setBrush(QPalette.Background, QBrush(gradient))
        self.setPalette(palette)
        self.setAutoFillBackground(True)
        self.setStyleSheet('''
        QLabel#user_icon { background-color: #b4fffa; color: #2a319d; padding: 10; border: none; }
        QLabel#username { color: #b4fffa; padding: 2; }
        QPushButton#login { color: #2a319d; border: none; background-color: qlineargradient( \
            x1: 0, y1: 0, x2: 0, y2: 1, stop: 0 #b4fffa, stop: 1 #05edfe); }
        QPushButton#login:pressed { background-color: #85f6fe; }
        ''')

        # Create a drop shadow effect
        effect = QGraphicsDropShadowEffect(self)
        effect.setOffset(0, 1)
        effect.setBlurRadius(8)
        effect.setColor(QColor('#aa000000'))

        # Create user icon
        self.user_icon = QLabel()
        self.user_icon.setObjectName('user_icon')
        self.user_icon.setFont(QFont("Helvetica [Cronyx]", 16, QFont.Bold))
        self.user_icon.hide()
        self.user_state = QLabel()
        self.user_state.setObjectName('username')
        self.user_state.setFont(QFont("Helvetica [Cronyx]", 14, QFont.Bold))
        self.user_state.hide()
        self.user_menu = JournalistMenuButton(self)
        self.user_menu.hide()

        # Create sign-in button
        self.login = QPushButton(_('SIGN IN'))
        self.login.setObjectName('login')
        self.login.setFont(QFont("Helvetica [Cronyx]", 10))
        self.login.setMinimumSize(200, 40)
        self.login.setGraphicsEffect(effect)
        self.login.update()
        self.login.clicked.connect(self.on_login_clicked)

        # Create spacer to push toolbar contents to the top
        spacer = QWidget()
        spacer.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)

        # Set up horizontal user auth layout
        user_auth_layout = QHBoxLayout()
        user_auth_layout.addWidget(self.user_icon, 5, Qt.AlignLeft)
        user_auth_layout.addWidget(self.user_state, 5, Qt.AlignLeft)
        user_auth_layout.addWidget(self.login, 5, Qt.AlignLeft)
        user_auth_layout.addWidget(self.user_menu, 5, Qt.AlignLeft)
        user_auth_layout.addStretch()

        # Add user auth layout to left sidebar
        layout.addLayout(user_auth_layout)
        layout.addStretch()

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
        self.login.hide()

        self.user_icon.setText(_('jo'))
        self.user_icon.show()

        self.user_state.setText(_('{}').format(html.escape(username)))
        self.user_state.show()

        self.user_menu.show()

    def set_logged_out(self):
        """
        Update the UI to a logged out state.
        """
        self.login.show()
        self.user_icon.hide()
        self.user_state.hide()
        self.user_menu.hide()

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
        self.layout.setContentsMargins(0, 0, 0, 0)
        self.layout.setSpacing(0)
        self.setLayout(self.layout)

        left_column = QWidget(parent=self)
        left_layout = QVBoxLayout()
        left_layout.setContentsMargins(0, 0, 0, 0)
        left_column.setLayout(left_layout)

        self.source_list = SourceList(left_column)
        left_layout.addWidget(self.source_list)

        self.layout.addWidget(left_column, 4)

        self.view_layout = QVBoxLayout()
        self.view_layout.setContentsMargins(0, 0, 0, 0)
        self.view_holder = QWidget()
        self.view_holder.setStyleSheet('background: #efeef7;')
        self.view_holder.setLayout(self.view_layout)

        self.layout.addWidget(self.view_holder, 6)

    def setup(self, controller):
        """
        Pass through the controller object to this widget.
        """
        self.controller = controller
        self.source_list.setup(controller)

    def set_conversation(self, widget):
        """
        Update the view holder to contain the referenced widget.
        """
        old_widget = self.view_layout.takeAt(0)

        if old_widget:
            old_widget.widget().hide()

        self.view_layout.addWidget(widget)
        widget.show()


class SourceList(QListWidget):
    """
    Displays the list of sources.
    """

    def __init__(self, parent):
        super().__init__(parent)
        self.setStyleSheet('QListWidget::item:selected { background: #efeef7 }')

    def setup(self, controller):
        """
        Pass through the controller object to this widget.
        """
        self.controller = controller

    def update(self, sources: List[Source]):
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

    def _construct_message(self, source: Source) -> str:
        files = 0
        messages = 0
        for submission in source.collection:
            if isinstance(submission, Message):
                messages += 1
            elif isinstance(submission, File):
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

    def __init__(self, parent: QWidget, source: Source):
        """
        Set up the child widgets.
        """
        super().__init__(parent)

        self.setStyleSheet('''
            QWidget#color_bar { background-color: #9211ff; }
        ''')

        self.source = source
        self.name = QLabel()
        self.updated = QLabel()

        layout = QVBoxLayout()
        self.setLayout(layout)

        self.summary = QWidget(self)
        self.summary.setObjectName('summary')
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
        main_layout.setContentsMargins(0, 0, 0, 0)
        main_layout.addStretch()
        self.setLayout(main_layout)

        form = QWidget()
        layout = QVBoxLayout()
        layout.setContentsMargins(0, 0, 0, 0)
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
        self.error_label.setStyleSheet('color: #f22b5d')

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

    css = "padding:8px; min-height:32px; border:1px solid #999;"

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
        layout.setContentsMargins(0, 0, 0, 0)

        label = SpeechBubble(message_id, message, update_signal)

        if align != "left":
            # Float right...
            layout.addStretch(5)
            label.setStyleSheet(label.css)

        layout.addWidget(label, 6)

        if align == "left":
            # Add space on right hand side...
            layout.addStretch(5)
            label.setStyleSheet(label.css)

        self.setLayout(layout)


class MessageWidget(ConversationWidget):
    """
    Represents an incoming message from the source.
    """

    def __init__(self, message_id: str, message: str, update_signal) -> None:
        super().__init__(message_id,
                         message,
                         update_signal,
                         align="left")
        self.setStyleSheet('''
        background-color: qlineargradient( x1: 0, y1: 0, x2: 0, y2: 1, \
        stop: 0 #fff, stop: 0.9 #fff, stop: 1 #9211ff);
        ''')


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
        self.setStyleSheet('''
        background-color: qlineargradient( x1: 0, y1: 0, x2: 0, y2: 1, \
        stop: 0 #fff, stop: 0.9 #fff, stop: 1 #05edfe);
        ''')
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
                 controller, file_ready_signal, align="left"):
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
        self.file_uuid = self.submission.uuid
        self.align = align

        self.layout = QHBoxLayout()
        self.update()
        self.setLayout(self.layout)

        file_ready_signal.connect(self._on_file_download)

    def update(self):
        icon = QLabel()
        icon.setPixmap(load_image('file.png'))

        if self.submission.is_downloaded:
            description = QLabel("Open")
        else:
            human_filesize = humanize_filesize(self.submission.size)
            description = QLabel("Download ({})".format(human_filesize))

        if self.align != "left":
            # Float right...
            self.layout.addStretch(5)

        self.layout.addWidget(icon)
        self.layout.addWidget(description, 5)

        if self.align == "left":
            # Add space on right hand side...
            self.layout.addStretch(5)

    def clear(self):
        while self.layout.count():
            child = self.layout.takeAt(0)
            if child.widget():
                child.widget().deleteLater()

    @pyqtSlot(str)
    def _on_file_download(self, file_uuid: str) -> None:
        if file_uuid == self.file_uuid:
            self.clear()  # delete existing icon and label
            self.update()  # draw modified widget

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
        self.conversation_layout.setContentsMargins(0, 0, 0, 0)
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
        main_layout.setContentsMargins(0, 0, 0, 0)
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
                self.add_message(conversation_item)
            elif conversation_item.filename.endswith('reply.gpg'):
                self.controller.session.refresh(conversation_item)
                if conversation_item.content is not None:
                    content = conversation_item.content
                else:
                    content = '<Message not yet available>'
                self.add_reply(conversation_item.uuid, content)
            else:
                self.add_file(self.source, conversation_item)

    def add_file(self, source_db_object, submission_db_object):
        """
        Add a file from the source.
        """
        self.conversation_layout.addWidget(
            FileWidget(source_db_object, submission_db_object,
                       self.controller, self.controller.file_ready))

    def update_conversation_position(self, min_val, max_val):
        """
        Handler called when a new item is added to the conversation. Ensures
        it's scrolled to the bottom and thus visible.
        """
        current_val = self.scroll.verticalScrollBar().value()
        viewport_height = self.scroll.viewport().height()

        if current_val + viewport_height > max_val:
            self.scroll.verticalScrollBar().setValue(max_val)

    def add_message(self, message: Message) -> None:
        """
        Add a message from the source.
        """
        self.controller.session.refresh(message)
        if message.content is not None:
            content = message.content
        else:
            content = '<Message not yet available>'

        self.conversation_layout.addWidget(
            MessageWidget(message.uuid, content, self.controller.message_sync.message_ready))

    def add_reply(self, uuid: str, content: str) -> None:
        """
        Add a reply from a journalist.
        """
        self.conversation_layout.addWidget(
            ReplyWidget(uuid,
                        content,
                        self.controller.reply_sync.reply_ready,
                        self.controller.reply_succeeded,
                        self.controller.reply_failed,
                        ))


class SourceConversationWrapper(QWidget):
    """
    Wrapper for a source's conversation including the chat window, profile tab, and other
    per-source resources.
    """

    def __init__(
        self,
        source: Source,
        sdc_home: str,
        controller: Client,
        is_authenticated: bool,
        parent=None
    ) -> None:
        super().__init__(parent)
        self.source = source
        self.controller = controller
        self.sdc_home = sdc_home

        self.layout = QVBoxLayout()
        self.layout.setContentsMargins(0, 0, 0, 0)
        self.setLayout(self.layout)

        self.conversation = ConversationView(self.source, self.sdc_home, self.controller,
                                             parent=self)
        self.source_profile = SourceProfileShortWidget(self.source, self.controller)

        self.layout.addWidget(self.source_profile, 1)
        self.layout.addWidget(self.conversation, 9)

        self.controller.authentication_state.connect(self._show_or_hide_replybox)
        self._show_or_hide_replybox(is_authenticated)

    def send_reply(self, message: str) -> None:
        msg_uuid = str(uuid4())
        self.conversation.add_reply(msg_uuid, message)
        self.controller.send_reply(self.source.uuid, msg_uuid, message)

    def _show_or_hide_replybox(self, show: bool) -> None:
        if show:
            new_widget = ReplyBoxWidget(self)
        else:
            new_widget = ReplyBoxWidget(self)
            new_widget.text_edit.setText(_('You need to log in to send replies.'))
            new_widget.text_edit.setEnabled(False)
            new_widget.send_button.hide()

        old_widget = self.layout.takeAt(2)
        if old_widget is not None:
            old_widget.widget().deleteLater()

        self.reply_box = new_widget
        self.layout.addWidget(new_widget, 3)


class ReplyBoxWidget(QWidget):
    """
    A textbox where a journalist can enter a reply.
    """

    def __init__(self, conversation: SourceConversationWrapper) -> None:
        super().__init__()

        self.setStyleSheet('background: #fff;')

        self.conversation = conversation

        self.text_edit = QTextEdit()

        self.send_button = QPushButton()
        self.send_button.clicked.connect(self.send_reply)
        self.send_button.setMaximumSize(40, 40)

        button_pixmap = load_image('send.png')
        button_icon = QIcon(button_pixmap)
        self.send_button.setIcon(button_icon)
        self.send_button.setIconSize(button_pixmap.rect().size())

        layout = QVBoxLayout()
        layout.setContentsMargins(0, 0, 0, 0)
        layout.addWidget(self.text_edit)

        layout.addWidget(self.send_button, 0, Qt.AlignRight)
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


class JournalistMenu(QMenu):
    """A menu next to the journalist username.

    A menu that provides login options.
    """

    def __init__(self, parent):
        super().__init__()
        self.logout = QAction(_('SIGN OUT'))
        self.logout.setFont(QFont("Helvetica [Cronyx]", 10))
        self.addAction(self.logout)
        self.logout.triggered.connect(parent.on_logout_clicked)


class JournalistMenuButton(QToolButton):
    """An menu button for the journalist menu

    This button is responsible for launching the journalist menu on click.
    """

    def __init__(self, parent):
        super().__init__()

        self.setStyleSheet('''
            QToolButton::menu-indicator { image: none; }
            QToolButton { border: none; }
        ''')
        arrow = load_image("dropdown_arrow.svg")
        self.setIcon(QIcon(arrow))
        self.setMinimumSize(20, 20)

        self.menu = JournalistMenu(parent)
        self.setMenu(self.menu)

        self.setPopupMode(QToolButton.InstantPopup)


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

    This button is responsible for launching the source menu on click.
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
    """The title for a conversation."""

    def __init__(self, text):
        html_text = _('<h1>{}</h1>').format(text)
        super().__init__(html_text)


class LastUpdatedLabel(QLabel):
    """Time the conversation was last updated."""

    def __init__(self, last_updated):
        html_text = _('<h3>{}</h3>').format(arrow.get(last_updated).humanize())
        super().__init__(html_text)


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

        self.title = TitleLabel(self.source.journalist_designation)
        self.updated = LastUpdatedLabel(self.source.last_updated)
        self.menu = SourceMenuButton(self.source, self.controller)

        self.layout.addWidget(self.title, 10, Qt.AlignLeft)
        self.layout.addWidget(self.updated, 1, Qt.AlignRight)
        self.layout.addWidget(self.menu, 1, Qt.AlignRight)
