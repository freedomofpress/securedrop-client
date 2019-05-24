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
import sys

from gettext import gettext as _
from typing import List
from uuid import uuid4
from PyQt5.QtCore import Qt, pyqtSlot, pyqtSignal, QTimer, QSize, pyqtBoundSignal, QObject
from PyQt5.QtGui import QIcon, QPalette, QBrush, QColor, QFont, QLinearGradient
from PyQt5.QtWidgets import QListWidget, QLabel, QWidget, QListWidgetItem, QHBoxLayout, \
    QPushButton, QVBoxLayout, QLineEdit, QScrollArea, QDialog, QAction, QMenu, QMessageBox, \
    QToolButton, QSizePolicy, QTextEdit, QStatusBar, QGraphicsDropShadowEffect

from securedrop_client.db import Source, Message, File, Reply
from securedrop_client.storage import source_exists
from securedrop_client.gui import SvgLabel, SvgPushButton, SvgToggleButton
from securedrop_client.logic import Controller
from securedrop_client.resources import load_icon, load_image
from securedrop_client.utils import humanize_filesize

logger = logging.getLogger(__name__)


class TopPane(QWidget):
    """
    Top pane of the app window.
    """

    def __init__(self):
        super().__init__()

        # Fill the background with a gradient
        palette = QPalette()
        gradient = QLinearGradient(0, 0, 900, 0)
        gradient.setColorAt(0, QColor('#0565d4'))
        gradient.setColorAt(1, QColor('#002c55'))
        palette.setBrush(QPalette.Background, QBrush(gradient))
        self.setPalette(palette)
        self.setAutoFillBackground(True)

        # Set layout
        layout = QHBoxLayout(self)
        self.setLayout(layout)

        # Remove margins and spacing
        layout.setContentsMargins(10, 0, 0, 0)
        layout.setSpacing(0)

        # Refresh button
        self.refresh = RefreshButton()
        self.refresh.disable()

        # Activity status bar
        self.activity_status_bar = ActivityStatusBar()

        # Error status bar
        self.error_status_bar = ErrorStatusBar()

        # Create space the size of the status bar to keep the error status bar centered
        spacer = QWidget()

        # Create space ths size of the refresh button to keep the error status bar centered
        spacer2 = QWidget()
        spacer2.setFixedWidth(42)

        # Set height of top pane to 42 pixels
        self.setFixedHeight(42)
        self.refresh.setFixedHeight(42)
        self.activity_status_bar.setFixedHeight(42)
        self.error_status_bar.setFixedHeight(42)
        spacer.setFixedHeight(42)
        spacer2.setFixedHeight(42)

        # Add widgets to layout
        layout.addWidget(self.refresh, 1)
        layout.addWidget(self.activity_status_bar, 1)
        layout.addWidget(self.error_status_bar, 5)
        layout.addWidget(spacer, 1)
        layout.addWidget(spacer2, 1)

    def setup(self, controller):
        self.refresh.setup(controller)

    def enable_refresh(self):
        self.refresh.enable()

    def disable_refresh(self):
        self.refresh.disable()

    def update_activity_status(self, message: str, duration: int):
        self.activity_status_bar.update_message(message, duration)

    def update_error_status(self, message: str, duration: int):
        self.error_status_bar.update_message(message, duration)

    def clear_error_status(self):
        self.error_status_bar.clear_message()


class LeftPane(QWidget):
    """
    Represents the left side pane that contains user authentication actions and information.
    """

    def __init__(self):
        super().__init__()

        # Set layout
        layout = QVBoxLayout(self)
        self.setLayout(layout)

        # Remove margins and spacing
        layout.setContentsMargins(12, 12, 12, 12)
        layout.setSpacing(0)

        # Use a background gradient
        palette = QPalette()
        gradient = QLinearGradient(0, 0, 0, 700)
        gradient.setColorAt(0, QColor('#0093da'))
        gradient.setColorAt(1, QColor('#0c3e75'))
        palette.setBrush(QPalette.Background, QBrush(gradient))
        self.setPalette(palette)
        self.setAutoFillBackground(True)

        # User profile
        self.user_profile = UserProfile()

        # Hide user profile widget until user logs in
        self.user_profile.hide()

        # Add widgets to layout
        layout.addWidget(self.user_profile)

        # Align content to the top of pane
        layout.addStretch()

    def setup(self, window, controller):
        self.user_profile.setup(window, controller)

    def set_logged_in_as(self, username):
        """
        Update the UI to reflect that the user is logged in as "username".
        """
        self.user_profile.set_username(username)
        self.user_profile.show()

    def set_logged_out(self):
        """
        Update the UI to a logged out state.
        """
        self.user_profile.hide()


class RefreshButton(SvgPushButton):
    """
    A button that shows an icon for different refresh states.
    """

    CSS = '''
    #refresh_button {
        border: none;
        color: #fff;
    }
    '''

    def __init__(self):
        # Add svg images to button
        super().__init__(
            normal='refresh.svg',
            disabled='refresh_offline.svg',
            active='refresh_active.svg',
            selected='refresh.svg',
            svg_size=QSize(18, 18))

        # Set css id
        self.setObjectName('refresh_button')

        # Set styles
        self.setStyleSheet(self.CSS)
        self.setFixedSize(QSize(22, 22))

        # Click event handler
        self.clicked.connect(self._on_clicked)

    def setup(self, controller):
        """
        Assign a controller object (containing the application logic).
        """
        self.controller = controller
        self.controller.sync_events.connect(self._on_refresh_complete)

    def _on_clicked(self):
        self.controller.sync_api()
        # This is a temporary solution for showing the icon as active for the entire duration of a
        # refresh, rather than for just the duration of a click. The icon image will be replaced
        # when the controller tells us the refresh has finished. A cleaner solution would be to
        # store and update our own icon mode so we don't have to reload any images.
        self.setIcon(load_icon(
            normal='refresh_active.svg',
            disabled='refresh_offline.svg'))

    def _on_refresh_complete(self, data):
        if (data == 'synced'):
            self.setIcon(load_icon(
                normal='refresh.svg',
                disabled='refresh_offline.svg',
                active='refresh_active.svg',
                selected='refresh.svg'))

    def enable(self):
        self.setEnabled(True)

    def disable(self):
        self.setEnabled(False)


class ActivityStatusBar(QStatusBar):
    """
    A status bar for displaying messages about application activity to the user. Messages will be
    displayed for a given duration or until the message updated with a new message.
    """

    CSS = '''
    #activity_status_bar {
        color: #fff;
    }
    '''

    def __init__(self):
        super().__init__()

        # Set css id
        self.setObjectName('activity_status_bar')

        # Set styles
        self.setStyleSheet(self.CSS)

        # Remove grip image at bottom right-hand corner
        self.setSizeGripEnabled(False)

    def update_message(self, message: str, duration: int):
        """
        Display a status message to the user.
        """
        self.showMessage(message, duration)


class ErrorStatusBar(QWidget):
    """
    A pop-up status bar for displaying messages about application errors to the user. Messages will
    be displayed for a given duration or until the message is cleared or updated with a new message.
    """

    CSS = '''
    #error_vertical_bar {
        background-color: #f22b5d;
    }
    #error_icon {
        background-color: qlineargradient(
            x1: 0,
            y1: 0,
            x2: 0,
            y2: 1,
            stop: 0 #fff,
            stop: 0.2 #fff,
            stop: 1 #fff
        );
    }
    #error_status_bar {
        background-color: qlineargradient(
            x1: 0,
            y1: 0,
            x2: 0,
            y2: 1,
            stop: 0 #fff,
            stop: 0.2 #fff,
            stop: 1 #fff
        );
        font-weight: bold;
        color: #f22b5d;
    }
    '''

    def __init__(self):
        super().__init__()

        # Set styles
        self.setStyleSheet(self.CSS)

        # Set layout
        layout = QHBoxLayout(self)
        self.setLayout(layout)

        # Remove margins and spacing
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Error vertical bar
        self.vertical_bar = QWidget()
        self.vertical_bar.setObjectName('error_vertical_bar')  # Set css id
        self.vertical_bar.setFixedWidth(10)

        # Error icon
        self.label = SvgLabel('error_icon.svg', svg_size=QSize(32, 32))
        self.label.setObjectName('error_icon')  # Set css id
        self.label.setFixedWidth(42)

        # Error status bar
        self.status_bar = QStatusBar()
        self.status_bar.setObjectName('error_status_bar')  # Set css id
        self.status_bar.setSizeGripEnabled(False)

        # Add widgets to layout
        layout.addWidget(self.vertical_bar)
        layout.addWidget(self.label)
        layout.addWidget(self.status_bar)

        # Hide until a message needs to be displayed
        self.vertical_bar.hide()
        self.label.hide()
        self.status_bar.hide()

        # Only show errors for a set duration
        self.status_timer = QTimer()
        self.status_timer.timeout.connect(self._on_status_timeout)

    def _hide(self):
        self.vertical_bar.hide()
        self.label.hide()
        self.status_bar.hide()

    def _show(self):
        self.vertical_bar.show()
        self.label.show()
        self.status_bar.show()

    def _on_status_timeout(self):
        self._hide()

    def update_message(self, message: str, duration: int):
        """
        Display a status message to the user for a given duration.
        """
        self.status_bar.showMessage(message, duration)
        self.status_timer.start(duration)
        self._show()

    def clear_message(self):
        """
        Clear any message currently in the status bar.
        """
        self.status_bar.clearMessage()
        self._hide()


class UserProfile(QWidget):
    """
    A widget that contains user profile information and options.

    Displays user profile icon, name, and menu options if the user is logged in. Displays a login
    button if the user is logged out.
    """

    CSS = '''
    QLabel#user_icon {
        border: none;
        padding: 10px;
        background-color: #b4fffa;
        font-family: Open Sans;
        font-size: 16px;
        font-weight: bold;
        color: #2a319d;
    }
    '''

    def __init__(self):
        super().__init__()

        # Set css id
        self.setObjectName('user_profile')

        # Set styles
        self.setStyleSheet(self.CSS)
        self.setFixedWidth(200)

        # Set layout
        layout = QHBoxLayout(self)
        self.setLayout(layout)

        # Remove margins
        layout.setContentsMargins(0, 0, 0, 0)

        # Login button
        self.login_button = LoginButton()

        # User icon
        self.user_icon = QLabel()
        self.user_icon.setObjectName('user_icon')  # Set css id

        # User button
        self.user_button = UserButton()

        # Add widgets to user auth layout
        layout.addWidget(self.login_button, 1)
        layout.addWidget(self.user_icon, 1)
        layout.addWidget(self.user_button, 4)

        # Align content to the left
        layout.addStretch()

    def setup(self, window, controller):
        self.user_button.setup(controller)
        self.login_button.setup(window)

    def set_username(self, username):
        self.user_icon.setText(_('jo'))
        self.user_button.set_username(username)

    def show(self):
        self.login_button.hide()
        self.user_icon.show()
        self.user_button.show()

    def hide(self):
        self.user_icon.hide()
        self.user_button.hide()
        self.login_button.show()


class UserButton(SvgPushButton):
    """An menu button for the journalist menu

    This button is responsible for launching the journalist menu on click.
    """

    CSS = '''
    SvgPushButton#user_button {
        border: none;
        padding-left: 6px;
        background-color: #0093da;
        font-family: Open Sans;
        font-size: 14px;
        font-weight: bold;
        color: #b4fffa;
        text-align: left;
    }
    SvgPushButton::menu-indicator {
        image: none;
    }
    '''

    def __init__(self):
        super().__init__('dropdown_arrow.svg', svg_size=QSize(9, 6))

        # Set css id
        self.setObjectName('user_button')

        # Set styles
        self.setStyleSheet(self.CSS)
        self.setFixedHeight(40)

        self.setLayoutDirection(Qt.RightToLeft)

        self.menu = UserMenu()
        self.setMenu(self.menu)

    def setup(self, controller):
        self.menu.setup(controller)

    def set_username(self, username):
        self.setText(_('{}').format(html.escape(username)))


class UserMenu(QMenu):
    """A menu next to the journalist username.

    A menu that provides login options.
    """

    def __init__(self):
        super().__init__()
        self.logout = QAction(_('SIGN OUT'))
        self.logout.setFont(QFont("OpenSans", 10))
        self.addAction(self.logout)
        self.logout.triggered.connect(self._on_logout_triggered)

    def setup(self, controller):
        """
        Store a reference to the controller (containing the application logic).
        """
        self.controller = controller

    def _on_logout_triggered(self):
        """
        Called when the logout button is selected from the menu.
        """
        self.controller.logout()


class LoginButton(QPushButton):
    """
    A button that opens a login dialog when clicked.
    """

    CSS = '''
    #login {
        border: none;
        background-color: qlineargradient(
            x1: 0,
            y1: 0,
            x2: 0,
            y2: 1,
            stop: 0 #b4fffa,
            stop: 1 #05edfe
        );
        font-family: Open Sans;
        font-size: 14px;
        color: #2a319d;
    }
    #login:pressed {
        background-color: #85f6fe;
    }
    '''

    def __init__(self):
        super().__init__(_('SIGN IN'))

        # Set css id
        self.setObjectName('login')

        # Set styles
        self.setStyleSheet(self.CSS)
        self.setFixedHeight(40)

        # Set drop shadow effect
        effect = QGraphicsDropShadowEffect(self)
        effect.setOffset(0, 1)
        effect.setBlurRadius(8)
        effect.setColor(QColor('#aa000000'))
        self.setGraphicsEffect(effect)
        self.update()

        # Set click handler
        self.clicked.connect(self._on_clicked)

    def setup(self, window):
        """
        Store a reference to the GUI window object.
        """
        self.window = window

    def _on_clicked(self):
        """
        Called when the login button is clicked.
        """
        self.window.show_login()


class MainView(QWidget):
    """
    Represents the main content of the application (containing the source list
    and main context view).
    """

    CSS = '''
    #view_holder {
        background-color: #fff;
    }
    '''

    def __init__(self, parent: QObject):
        super().__init__(parent)

        self.setStyleSheet(self.CSS)

        self.layout = QHBoxLayout(self)
        self.layout.setContentsMargins(0, 0, 0, 0)
        self.layout.setSpacing(0)
        self.setLayout(self.layout)

        self.source_list = SourceList()
        self.source_list.itemSelectionChanged.connect(self.on_source_changed)

        self.view_layout = QVBoxLayout()
        self.view_layout.setContentsMargins(0, 0, 0, 0)
        self.view_holder = QWidget()
        self.view_holder.setObjectName('view_holder')  # Set css id
        self.view_holder.setLayout(self.view_layout)

        self.layout.addWidget(self.source_list)
        self.layout.addWidget(self.view_holder)

    def setup(self, controller):
        """
        Pass through the controller object to this widget.
        """
        self.controller = controller
        self.source_list.setup(controller)

    def show_sources(self, sources: List[Source]):
        """
        Update the left hand sources list in the UI with the passed in list of
        sources.
        """
        self.source_list.update(sources)

    def on_source_changed(self):
        """
        Show conversation for the currently-selected source if it hasn't been deleted. If the
        current source no longer exists, clear the conversation for that source.
        """
        source = self.source_list.get_current_source()

        if source:
            conversation_wrapper = SourceConversationWrapper(source, self.controller)
            self.set_conversation(conversation_wrapper)
        else:
            self.clear_conversation()

    def set_conversation(self, widget):
        """
        Update the view holder to contain the referenced widget.
        """
        old_widget = self.view_layout.takeAt(0)

        if old_widget:
            old_widget.widget().hide()

        self.view_layout.addWidget(widget)
        widget.show()

    def clear_conversation(self):
        while self.view_layout.count():
            child = self.view_layout.takeAt(0)
            if child.widget():
                child.widget().deleteLater()


class SourceList(QListWidget):
    """
    Displays the list of sources.
    """

    CSS = '''
    QListWidget::item:selected {
        background: #efeef7;
    }
    '''

    def __init__(self):
        super().__init__()

        # Set css id
        self.setObjectName('sourcelist')

        # Set styles
        self.setStyleSheet(self.CSS)
        self.setMinimumWidth(445)
        self.setMaximumWidth(565)

        # Set layout
        layout = QVBoxLayout(self)
        self.setLayout(layout)

        # Remove margins
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

    def setup(self, controller):
        self.controller = controller

    def update(self, sources: List[Source]):
        """
        Reset and update the list with the passed in list of sources.
        """
        current_source = self.get_current_source()
        current_source_id = current_source and current_source.id

        self.clear()

        for source in sources:
            new_source = SourceWidget(source)
            new_source.setup(self.controller)

            list_item = QListWidgetItem(self)
            list_item.setSizeHint(new_source.sizeHint())

            self.addItem(list_item)
            self.setItemWidget(list_item, new_source)

            if source.id == current_source_id:
                self.setCurrentItem(list_item)

    def get_current_source(self):
        source_item = self.currentItem()
        source_widget = self.itemWidget(source_item)
        if source_widget and source_exists(self.controller.session, source_widget.source.uuid):
            return source_widget.source


class SourceWidget(QWidget):
    """
    Used to display summary information about a source in the list view.
    """

    CSS = '''
    QWidget#color_bar {
        background-color: #9211ff;
    }
    QLabel#source_name {
        font-family: Open Sans;
        font-size: 16px;
        font-weight: bold;
        color: #000;
    }
    QLabel#timestamp {
        font-family: Open Sans;
        font-size: 12px;
        color: #000;
    }
    '''

    def __init__(self, source: Source):
        super().__init__()

        # Store source
        self.source = source

        # Set css id
        self.setObjectName('source_widget')

        # Set styles
        self.setStyleSheet(self.CSS)

        # Set layout
        layout = QVBoxLayout(self)
        self.setLayout(layout)

        # Remove margins and spacing
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(0)

        # Set up gutter
        self.gutter = QWidget()
        self.gutter.setObjectName('gutter')
        self.gutter.setFixedWidth(30)
        gutter_layout = QVBoxLayout(self.gutter)
        gutter_layout.setContentsMargins(0, 0, 0, 0)
        gutter_layout.setSpacing(0)
        self.star = StarToggleButton(self.source)
        spacer = QWidget()
        gutter_layout.addWidget(self.star)
        gutter_layout.addWidget(spacer)

        # Set up summary
        self.summary = QWidget()
        self.summary.setObjectName('summary')
        summary_layout = QVBoxLayout(self.summary)
        summary_layout.setContentsMargins(0, 0, 0, 0)
        summary_layout.setSpacing(0)
        self.name = QLabel()
        self.name.setObjectName('source_name')
        self.preview = QLabel('')
        self.preview.setObjectName('preview')
        self.preview.setWordWrap(True)
        summary_layout.addWidget(self.name)
        summary_layout.addWidget(self.preview)

        # Set up metadata
        self.metadata = QWidget()
        self.metadata.setObjectName('metadata')
        metadata_layout = QVBoxLayout(self.metadata)
        metadata_layout.setContentsMargins(0, 0, 0, 0)
        metadata_layout.setSpacing(0)
        self.attached = SvgLabel('paperclip.svg', QSize(16, 16))
        self.attached.setObjectName('paperclip')
        self.attached.setFixedSize(QSize(20, 20))
        spacer = QWidget()
        metadata_layout.addWidget(self.attached, 1, Qt.AlignRight)
        metadata_layout.addWidget(spacer, 1)

        # Set up source row
        self.source_row = QWidget()
        source_row_layout = QHBoxLayout(self.source_row)
        source_row_layout.setContentsMargins(0, 0, 0, 0)
        source_row_layout.setSpacing(0)
        source_row_layout.addWidget(self.gutter, 1)
        source_row_layout.addWidget(self.summary, 1)
        source_row_layout.addWidget(self.metadata, 1)

        # Set up timestamp
        self.updated = QLabel()
        self.updated.setObjectName('timestamp')

        # Add widgets to main layout
        layout.addWidget(self.source_row, 1)
        layout.addWidget(self.updated, 1, Qt.AlignRight)

        self.update()

    def setup(self, controller):
        """
        Pass through the controller object to this widget.
        """
        self.controller = controller
        self.star.setup(self.controller)

    def update(self):
        """
        Updates the displayed values with the current values from self.source.
        """
        self.updated.setText(arrow.get(self.source.last_updated).humanize())
        self.name.setText("<strong>{}</strong>".format(
                          html.escape(self.source.journalist_designation)))
        if self.source.document_count == 0:
            self.attached.hide()

    def delete_source(self, event):
        if self.controller.api is None:
            self.controller.on_action_requiring_login()
            return
        else:
            messagebox = DeleteSourceMessageBox(self, self.source, self.controller)
            messagebox.launch()


class StarToggleButton(SvgToggleButton):
    """
    A button that shows whether or not a source is starred
    """

    css = '''
    #star_button {
        border: none;
    }
    '''

    def __init__(self, source: Source):
        super().__init__(
            on='star_on.svg',
            off='star_off.svg',
            svg_size=QSize(16, 16))

        self.source = source
        if self.source.is_starred:
            self.setChecked(True)

        self.setObjectName('star_button')
        self.setStyleSheet(self.css)
        self.setFixedSize(QSize(20, 20))

    def setup(self, controller):
        self.controller = controller
        self.controller.authentication_state.connect(self.on_authentication_changed)
        self.on_authentication_changed(self.controller.is_authenticated)

    def on_authentication_changed(self, authenticated: bool):
        """
        Set up handlers based on whether or not the user is authenticated. Connect to 'pressed'
        event instead of 'toggled' event when not authenticated because toggling will be disabled.
        """
        if authenticated:
            self.toggled.connect(self.on_toggle)
        else:
            self.pressed.connect(self.on_toggle_offline)

    def on_toggle(self):
        """
        Tell the controller to make an API call to update the source's starred field.
        """
        self.controller.update_star(self.source)

    def on_toggle_offline(self):
        """
        Show error message and disable toggle by setting checkable to False. Unfortunately,
        disabling toggle doesn't freeze state, rather it always displays the off state when a user
        tries to toggle. In order to save on state we update the icon's off state image to display
        on (hack).
        """
        self.controller.on_action_requiring_login()
        self.setCheckable(False)
        if self.source.is_starred:
            self.set_icon(on='star_on.svg', off='star_on.svg')


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
            self.parent, "", _(message), QMessageBox.Cancel | QMessageBox.Yes, QMessageBox.Cancel)

        if reply == QMessageBox.Yes:
            logger.debug("Deleting source %s" % (self.source.uuid,))
            self.controller.delete_source(self.source)

    def _construct_message(self, source: Source) -> str:
        files = 0
        messages = 0
        replies = 0
        for submission in source.collection:
            if isinstance(submission, Message):
                messages += 1
            if isinstance(submission, Reply):
                replies += 1
            elif isinstance(submission, File):
                files += 1

        message_tuple = (
            "<big>Deleting the Source account for",
            "<b>{}</b> will also".format(source.journalist_designation,),
            "delete {} files, {} replies, and {} messages.</big>".format(files, replies, messages),
            "<br>",
            "<small>This Source will no longer be able to correspond",
            "through the log-in tied to this account.</small>",
        )
        message = ' '.join(message_tuple)
        return message


class LoginDialog(QDialog):
    """
    A dialog to display the login form.
    """

    CSS = '''
    #error_label {
        color: #f22b5d;
    }
    '''

    MIN_PASSWORD_LEN = 14  # Journalist.MIN_PASSWORD_LEN on server
    MAX_PASSWORD_LEN = 128  # Journalist.MAX_PASSWORD_LEN on server
    MIN_JOURNALIST_USERNAME = 3  # Journalist.MIN_USERNAME_LEN on server

    def __init__(self, parent):
        self.parent = parent
        super().__init__(self.parent)

    def closeEvent(self, event):
        """
        Only exit the application when the main window is not visible.
        """
        if not self.parent.isVisible():
            sys.exit(0)

    def keyPressEvent(self, event):
        """
        Override default QDialog behavior that closes the dialog window when the Esc key is pressed.
        Instead, ignore the event.
        """
        if event.key() == Qt.Key_Escape:
            event.ignore()

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
                                     'offline, without signing in. To '
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

        self.offline_mode = QPushButton(_('Offline mode'))
        self.offline_mode.clicked.connect(self.controller.login_offline_mode)

        self.error_label = QLabel('')
        self.error_label.setObjectName('error_label')  # Set css id
        self.error_label.setStyleSheet(self.CSS)  # Set styles

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
        layout.addWidget(self.offline_mode)
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

    CSS = '''
    #speech_bubble {
        padding: 8px;
        min-height:32px;
        border:1px solid #999;
    }
    '''

    def __init__(self, message_id: str, text: str, update_signal) -> None:
        super().__init__()
        self.message_id = message_id

        # Set styles
        self.setStyleSheet(self.CSS)

        layout = QVBoxLayout()
        self.setLayout(layout)
        self.message = QLabel(html.escape(text, quote=False))
        self.message.setObjectName('speech_bubble')
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

        self.speech_bubble = SpeechBubble(message_id, message, update_signal)

        # Add padding on left if we want to push the speech bubble to the right
        if align != "left":
            layout.addStretch(5)

        layout.addWidget(self.speech_bubble, 6)

        # Add padding on right if we want to push the speech bubble to the left
        if align == "left":
            layout.addStretch(5)

        self.setLayout(layout)


class MessageWidget(ConversationWidget):
    """
    Represents an incoming message from the source.
    """

    CSS = '''
    background-color: qlineargradient(
        x1: 0,
        y1: 0,
        x2: 0,
        y2: 1,
        stop: 0 #fff,
        stop: 0.9 #fff,
        stop: 1 #9211ff
    );
    '''

    def __init__(self, message_id: str, message: str, update_signal) -> None:
        super().__init__(message_id,
                         message,
                         update_signal,
                         align="left")

        # Set css id
        self.setObjectName('message_widget')

        # Set styles
        self.setStyleSheet(self.CSS)


class ReplyWidget(ConversationWidget):
    """
    Represents a reply to a source.
    """

    CSS = '''
    background-color: qlineargradient(
        x1: 0,
        y1: 0,
        x2: 0,
        y2: 1,
        stop: 0 #fff,
        stop: 0.9 #fff,
        stop: 1 #05edfe
    );
    '''

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

        # Set css id
        self.setObjectName('reply_widget')

        # Set styles
        self.setStyleSheet(self.CSS)

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


class FileWidget(QWidget):
    """
    Represents a file.
    """

    def __init__(
        self,
        file_uuid: str,
        controller: Controller,
        file_ready_signal: pyqtBoundSignal,
    ) -> None:
        """
        Given some text and a reference to the controller, make something to display a file.
        """
        super().__init__()
        self.controller = controller
        self.file = self.controller.get_file(file_uuid)

        self.layout = QHBoxLayout()
        self.update()
        self.setLayout(self.layout)

        file_ready_signal.connect(self._on_file_downloaded, type=Qt.QueuedConnection)

    def update(self) -> None:
        icon = QLabel()
        icon.setPixmap(load_image('file.png'))

        if self.file.is_downloaded:
            description = QLabel("Open")
        else:
            human_filesize = humanize_filesize(self.file.size)
            description = QLabel("Download ({})".format(human_filesize))

        self.layout.addWidget(icon)
        self.layout.addWidget(description, 5)
        self.layout.addStretch(5)

    def clear(self) -> None:
        while self.layout.count():
            child = self.layout.takeAt(0)
            if child.widget():
                child.widget().deleteLater()

    @pyqtSlot(str)
    def _on_file_downloaded(self, file_uuid: str) -> None:
        if file_uuid == self.file.uuid:
            # update state
            self.file = self.controller.get_file(self.file.uuid)

            # update gui
            self.clear()  # delete existing icon and label
            self.update()  # draw modified widget

    def mouseReleaseEvent(self, e):
        """
        Handle a completed click via the program logic. The download state
        of the file distinguishes which function in the logic layer to call.
        """
        # update state
        self.file = self.controller.get_file(self.file.uuid)

        if self.file.is_downloaded:
            # Open the already downloaded file.
            self.controller.on_file_open(self.file.uuid)
        else:
            # Download the file.
            self.controller.on_submission_download(File, self.file.uuid)


class ConversationView(QWidget):
    """
    Renders a conversation.

    Due to a bug, we cannot set a style sheet for this widget. See
    https://github.com/freedomofpress/securedrop-client/issues/304
    https://github.com/freedomofpress/securedrop-client/issues/273
    """

    def __init__(
        self,
        source_db_object: Source,
        controller: Controller,
    ):
        super().__init__()
        self.source = source_db_object
        self.controller = controller

        self.container = QWidget()
        self.container.setObjectName('container')
        self.conversation_layout = QVBoxLayout()
        self.conversation_layout.setContentsMargins(0, 0, 0, 0)
        self.container.setLayout(self.conversation_layout)
        self.container.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        self.scroll = QScrollArea()
        self.scroll.setObjectName('scroll')
        self.scroll.setVerticalScrollBarPolicy(Qt.ScrollBarAlwaysOn)
        self.scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.scroll.setWidget(self.container)
        self.scroll.setWidgetResizable(True)

        # Completely unintuitive way to ensure the view remains scrolled to the bottom.
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
                self.add_reply(conversation_item)
            else:
                self.add_file(self.source, conversation_item)

    def add_file(self, source_db_object, submission_db_object):
        """
        Add a file from the source.
        """
        self.conversation_layout.addWidget(
            FileWidget(
                submission_db_object.uuid,
                self.controller,
                self.controller.file_ready,
            ),
        )

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
        if message.content is not None:
            content = message.content
        else:
            content = '<Message not yet available>'

        self.conversation_layout.addWidget(MessageWidget(
            message.uuid,
            content,
            self.controller.message_sync.message_ready))

    def add_reply(self, reply: Reply) -> None:
        """
        Add a reply from a journalist to the source.
        """
        if reply.content is not None:
            content = reply.content
        else:
            content = '<Reply not yet available>'

        self.conversation_layout.addWidget(ReplyWidget(
            reply.uuid,
            content,
            self.controller.reply_sync.reply_ready,
            self.controller.reply_succeeded,
            self.controller.reply_failed))

    def add_reply_from_reply_box(self, uuid: str, content: str) -> None:
        """
        Add a reply from the reply box.
        """
        self.conversation_layout.addWidget(ReplyWidget(
            uuid,
            content,
            self.controller.reply_sync.reply_ready,
            self.controller.reply_succeeded,
            self.controller.reply_failed))

    def on_reply_sent(self, source_uuid: str, reply_uuid: str, reply_text: str) -> None:
        """
        Add the reply text sent from ReplyBoxWidget to the conversation.
        """
        if source_uuid == self.source.uuid:
            self.add_reply_from_reply_box(reply_uuid, reply_text)


class SourceConversationWrapper(QWidget):
    """
    Wrapper for a source's conversation including the chat window, profile tab, and other
    per-source resources.
    """

    def __init__(
        self,
        source: Source,
        controller: Controller,
    ) -> None:
        super().__init__()
        layout = QVBoxLayout()
        layout.setContentsMargins(0, 0, 0, 0)
        self.setLayout(layout)

        self.conversation_title_bar = SourceProfileShortWidget(source, controller)
        self.conversation_view = ConversationView(source, controller)
        self.reply_box = ReplyBoxWidget(source, controller)

        layout.addWidget(self.conversation_title_bar, 1)
        layout.addWidget(self.conversation_view, 9)
        layout.addWidget(self.reply_box, 3)

        # Connect reply_box to conversation_view
        self.reply_box.reply_sent.connect(self.conversation_view.on_reply_sent)


class ReplyBoxWidget(QWidget):
    """
    A textbox where a journalist can enter a reply.
    """

    reply_sent = pyqtSignal(str, str, str)

    def __init__(self, source: Source, controller: Controller) -> None:
        super().__init__()

        layout = QVBoxLayout()
        self.setLayout(layout)
        layout.setContentsMargins(0, 0, 0, 0)

        self.source = source
        self.controller = controller

        self.text_edit = QTextEdit()

        self.send_button = QPushButton()
        self.send_button.clicked.connect(self.send_reply)
        self.send_button.setMaximumSize(40, 40)

        button_pixmap = load_image('send.png')
        button_icon = QIcon(button_pixmap)
        self.send_button.setIcon(button_icon)
        self.send_button.setIconSize(button_pixmap.rect().size())

        self.controller.authentication_state.connect(self._on_authentication_changed)
        self._on_authentication_changed(self.controller.is_authenticated)

        layout.addWidget(self.text_edit)
        layout.addWidget(self.send_button, 0, Qt.AlignRight)

    def enable(self):
        self.text_edit.clear()
        self.text_edit.setEnabled(True)
        self.send_button.show()

    def disable(self):
        self.text_edit.setText(_('You need to log in to send replies.'))
        self.text_edit.setEnabled(False)
        self.send_button.hide()

    def send_reply(self) -> None:
        """
        Send reply and emit a signal so that the gui can be updated immediately, even before the
        the reply is saved locally.
        """
        reply_text = self.text_edit.toPlainText().strip()
        if reply_text:
            reply_uuid = str(uuid4())
            self.controller.send_reply(self.source.uuid, reply_uuid, reply_text)
            self.reply_sent.emit(self.source.uuid, reply_uuid, reply_text)
            self.text_edit.clear()

    def _on_authentication_changed(self, authenticated: bool) -> None:
        if authenticated:
            self.enable()
        else:
            self.disable()


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

    This button is responsible for launching the source menu on click.
    """

    def __init__(self, source, controller):
        super().__init__()
        self.controller = controller
        self.source = source

        self.setIcon(load_icon("ellipsis.svg"))

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
