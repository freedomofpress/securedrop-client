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
from typing import Dict, List, Union  # noqa: F401
from uuid import uuid4
from PyQt5.QtCore import Qt, pyqtSlot, pyqtSignal, QEvent, QTimer, QSize, pyqtBoundSignal, \
    QObject, QPoint
from PyQt5.QtGui import QIcon, QPalette, QBrush, QColor, QFont, QLinearGradient,\
    QKeySequence, QCursor
from PyQt5.QtWidgets import QListWidget, QLabel, QWidget, QListWidgetItem, QHBoxLayout, \
    QPushButton, QVBoxLayout, QLineEdit, QScrollArea, QDialog, QAction, QMenu, QMessageBox, \
    QToolButton, QSizePolicy, QPlainTextEdit, QStatusBar, QGraphicsDropShadowEffect

from securedrop_client.db import DraftReply, Source, Message, File, Reply, User
from securedrop_client.storage import source_exists
from securedrop_client.export import ExportStatus, ExportError
from securedrop_client.gui import SecureQLabel, SvgLabel, SvgPushButton, SvgToggleButton
from securedrop_client.logic import Controller
from securedrop_client.resources import load_icon, load_image, load_movie
from securedrop_client.utils import humanize_filesize

logger = logging.getLogger(__name__)


class TopPane(QWidget):
    """
    Top pane of the app window.
    """

    def __init__(self):
        super().__init__()

        # Fill the background with a gradient
        self.online_palette = QPalette()
        gradient = QLinearGradient(0, 0, 1553, 0)
        gradient.setColorAt(0, QColor('#1573d8'))
        gradient.setColorAt(0.22, QColor('#0060d3'))
        gradient.setColorAt(1, QColor('#002c53'))
        self.online_palette.setBrush(QPalette.Background, QBrush(gradient))

        self.offline_palette = QPalette()
        gradient = QLinearGradient(0, 0, 1553, 0)
        gradient.setColorAt(0, QColor('#1e1e1e'))
        gradient.setColorAt(0.22, QColor('#122d61'))
        gradient.setColorAt(1, QColor('#0d4a81'))
        self.offline_palette.setBrush(QPalette.Background, QBrush(gradient))

        self.setPalette(self.offline_palette)
        self.setAutoFillBackground(True)

        # Set layout
        layout = QHBoxLayout(self)
        self.setLayout(layout)

        # Remove margins and spacing
        layout.setContentsMargins(10, 0, 0, 0)
        layout.setSpacing(0)

        # Sync icon
        self.sync_icon = SyncIcon()

        # Activity status bar
        self.activity_status_bar = ActivityStatusBar()

        # Error status bar
        self.error_status_bar = ErrorStatusBar()

        # Create space the size of the status bar to keep the error status bar centered
        spacer = QWidget()

        # Create space ths size of the sync icon to keep the error status bar centered
        spacer2 = QWidget()
        spacer2.setFixedWidth(42)

        # Set height of top pane to 42 pixels
        self.setFixedHeight(42)
        self.sync_icon.setFixedHeight(42)
        self.activity_status_bar.setFixedHeight(42)
        self.error_status_bar.setFixedHeight(42)
        spacer.setFixedHeight(42)
        spacer2.setFixedHeight(42)

        # Add widgets to layout
        layout.addWidget(self.sync_icon, 1)
        layout.addWidget(self.activity_status_bar, 1)
        layout.addWidget(self.error_status_bar, 1)
        layout.addWidget(spacer, 1)
        layout.addWidget(spacer2, 1)

    def setup(self, controller):
        self.sync_icon.setup(controller)
        self.error_status_bar.setup(controller)

    def set_logged_in(self):
        self.sync_icon.enable()
        self.sync_icon.setCursor(QCursor(Qt.PointingHandCursor))
        self.setPalette(self.online_palette)

    def set_logged_out(self):
        self.sync_icon.disable()
        self.sync_icon.setCursor(QCursor(Qt.ArrowCursor))
        self.setPalette(self.offline_palette)

    def update_activity_status(self, message: str, duration: int):
        self.activity_status_bar.update_message(message, duration)

    def update_error_status(self, message: str, duration: int, retry: bool):
        self.error_status_bar.update_message(message, duration, retry)

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
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)
        layout.setAlignment(Qt.AlignBottom)
        self.setFixedWidth(198)
        self.setMinimumHeight(558)

        # Set background image
        self.logo = QWidget()
        self.online_palette = QPalette()
        # the sd logo on the background image becomes more faded in offline mode
        self.online_palette.setBrush(QPalette.Background, QBrush(load_image('left_pane.svg')))
        self.offline_palette = QPalette()
        self.offline_palette.setBrush(QPalette.Background,
                                      QBrush(load_image('left_pane_offline.svg')))
        self.logo.setPalette(self.offline_palette)
        self.logo.setAutoFillBackground(True)
        self.logo.setMaximumHeight(884)
        self.logo.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
        self.logo.setEnabled(False)

        # User profile
        self.user_profile = UserProfile()

        # Hide user profile widget until user logs in
        self.user_profile.hide()

        # Add widgets to layout
        layout.addWidget(self.user_profile)
        layout.addWidget(self.logo)

    def setup(self, window, controller):
        self.user_profile.setup(window, controller)

    def set_logged_in_as(self, db_user: User):
        """
        Update the UI to reflect that the user is logged in as "username".
        """
        self.user_profile.set_user(db_user)
        self.user_profile.show()
        self.logo.setPalette(self.online_palette)

    def set_logged_out(self):
        """
        Update the UI to a logged out state.
        """
        self.user_profile.hide()
        self.logo.setPalette(self.offline_palette)


class SyncIcon(QLabel):
    """
    An icon that shows sync state.
    """

    CSS = '''
    #sync_icon {
        border: none;
        color: #fff;
    }
    '''

    def __init__(self):
        # Add svg images to button
        super().__init__()
        self.setObjectName('sync_icon')
        self.setStyleSheet(self.CSS)
        self.setFixedSize(QSize(24, 20))
        self.sync_animation = load_movie("sync_disabled.gif")
        self.sync_animation.setScaledSize(QSize(24, 20))
        self.setMovie(self.sync_animation)
        self.sync_animation.start()

    def setup(self, controller):
        """
        Assign a controller object (containing the application logic).
        """
        self.controller = controller
        self.controller.sync_events.connect(self._on_sync)

    def _on_sync(self, data):
        if data == 'syncing':
            self.sync_animation = load_movie("sync_active.gif")
            self.sync_animation.setScaledSize(QSize(24, 20))
            self.setMovie(self.sync_animation)
            self.sync_animation.start()
            self.setCursor(QCursor(Qt.WaitCursor))
        elif data == 'synced':
            self.setCursor(QCursor(Qt.PointingHandCursor))

    def enable(self):
        self.sync_animation = load_movie("sync.gif")
        self.sync_animation.setScaledSize(QSize(24, 20))
        self.setMovie(self.sync_animation)
        self.sync_animation.start()

    def disable(self):
        self.sync_animation = load_movie("sync_disabled.gif")
        self.sync_animation.setScaledSize(QSize(24, 20))
        self.setMovie(self.sync_animation)
        self.sync_animation.start()


class ActivityStatusBar(QStatusBar):
    """
    A status bar for displaying messages about application activity to the user. Messages will be
    displayed for a given duration or until the message updated with a new message.
    """

    CSS = '''
    #activity_status_bar {
        font-family: 'Source Sans Pro';
        font-weight: 600;
        font-size: 12px;
        color: #d3d8ea;
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
        background-color: #ff3366;
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
        font-family: 'Source Sans Pro';
        font-weight: 400;
        font-size: 14px;
        color: #0c3e75;
    }
    QPushButton#retry_button {
        border: none;
        padding-right: 30px;
        background-color: #fff;
        color: #0065db;
        font-family: 'Source Sans Pro';
        font-weight: 600;
        font-size: 12px;
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
        self.label = SvgLabel('error_icon.svg', svg_size=QSize(20, 20))
        self.label.setObjectName('error_icon')  # Set css id
        self.label.setFixedWidth(42)

        # Error status bar
        self.status_bar = QStatusBar()
        self.status_bar.setObjectName('error_status_bar')  # Set css id
        self.status_bar.setSizeGripEnabled(False)

        # Retry button
        self.retry_button = QPushButton('RETRY')
        self.retry_button.setObjectName('retry_button')
        self.retry_button.setFixedHeight(42)

        # Add widgets to layout
        layout.addWidget(self.vertical_bar)
        layout.addWidget(self.label)
        layout.addWidget(self.status_bar)
        layout.addWidget(self.retry_button)

        # Hide until a message needs to be displayed
        self.vertical_bar.hide()
        self.label.hide()
        self.status_bar.hide()
        self.retry_button.hide()

        # Only show errors for a set duration
        self.status_timer = QTimer()
        self.status_timer.timeout.connect(self._on_status_timeout)

    def _hide(self):
        self.vertical_bar.hide()
        self.label.hide()
        self.status_bar.hide()
        self.retry_button.hide()

    def _show(self):
        self.vertical_bar.show()
        self.label.show()
        self.status_bar.show()

    def _on_status_timeout(self):
        self._hide()

    def setup(self, controller):
        self.controller = controller
        self.retry_button.clicked.connect(self._on_retry_clicked)

    def _on_retry_clicked(self) -> None:
        self.clear_message()
        self._hide()
        self.controller.resume_queues()

    def update_message(self, message: str, duration: int, retry: bool) -> None:
        """
        Display a status message to the user for a given duration. If the duration is zero,
        continuously show message.
        """
        if retry:
            self.retry_button.show()

        self.status_bar.showMessage(message, duration)

        if duration != 0:
            self.status_timer.start(duration)

        self._show()

    def clear_message(self):
        """
        Clear any message currently in the status bar.
        """
        self.status_bar.clearMessage()
        self._hide()


class UserProfile(QLabel):
    """
    A widget that contains user profile information and options.

    Displays user profile icon, name, and menu options if the user is logged in. Displays a login
    button if the user is logged out.
    """

    CSS = '''
    QLabel#user_profile {
        padding: 15px;
    }
    QLabel#user_icon {
        border: none;
        background-color: #9211ff;
        padding-left: 3px;
        padding-bottom: 4px;
        font-family: 'Source Sans Pro';
        font-weight: 600;
        font-size: 15px;
        color: #fff;
    }
    '''

    def __init__(self):
        super().__init__()

        # Set css id
        self.setObjectName('user_profile')

        # Set styles
        self.setStyleSheet(self.CSS)

        # Set background
        palette = QPalette()
        palette.setBrush(QPalette.Background, QBrush(QColor('#0096DC')))
        self.setPalette(palette)
        self.setAutoFillBackground(True)
        self.setMinimumHeight(20)
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Preferred)

        # Set layout
        layout = QHBoxLayout(self)
        self.setLayout(layout)

        # Remove margins
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Login button
        self.login_button = LoginButton()

        # User icon
        self.user_icon = QLabel()
        self.user_icon.setObjectName('user_icon')  # Set css id
        self.user_icon.setFixedSize(QSize(30, 30))
        self.user_icon.setAlignment(Qt.AlignCenter)
        self.user_icon_font = QFont()
        self.user_icon_font.setLetterSpacing(QFont.AbsoluteSpacing, 0.58)
        self.user_icon.setFont(self.user_icon_font)

        # User button
        self.user_button = UserButton()

        # Add widgets to user auth layout
        layout.addWidget(self.login_button, 1)
        layout.addWidget(self.user_icon, 1)
        layout.addWidget(self.user_button, 4)

        # Align content to the top left
        layout.addStretch()
        layout.setAlignment(Qt.AlignTop)

    def setup(self, window, controller):
        self.user_button.setup(controller)
        self.login_button.setup(window)

    def set_user(self, db_user: User):
        self.user_icon.setText(_(db_user.initials))
        self.user_button.set_username(db_user.fullname)

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
    SvgPushButton:focus {
        outline: none;
    }
    SvgPushButton#user_button {
        border: none;
        font-family: 'Source Sans Pro';
        font-weight: 700;
        font-size: 12px;
        color: #fff;
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
        self.setFixedHeight(30)

        self.setLayoutDirection(Qt.RightToLeft)

        self.menu = UserMenu()
        self.setMenu(self.menu)

        # Set cursor.
        self.setCursor(QCursor(Qt.PointingHandCursor))

    def setup(self, controller):
        self.menu.setup(controller)

    def set_username(self, username):
        formatted_name = _('{}').format(html.escape(username))
        self.setText(formatted_name)
        if len(formatted_name) > 21:
            # The name will be truncated, so create a tooltip to display full
            # name if the mouse hovers over the widget.
            self.setToolTip(_('{}').format(html.escape(username)))


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
        background-color: #05edfe;
        font-family: 'Montserrat';
        font-weight: 600;
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
    #main_view {
        min-height: 558;
    }
    #view_holder {
        min-width: 667;
        border: none;
        background-color: #f3f5f9;
    }
    QLabel#no-source {
        font-family: Montserrat-Regular;
        font-size: 35px;
        color: #a5b3e9;
        padding: 100px;
        qproperty-alignment: AlignLeft;
    }
    '''

    def __init__(self, parent: QObject):
        super().__init__(parent)

        # Set id and styles
        self.setObjectName('main_view')
        self.setStyleSheet(self.CSS)

        # Set layout
        self.layout = QHBoxLayout(self)
        self.setLayout(self.layout)

        # Set margins and spacing
        self.layout.setContentsMargins(0, 0, 0, 0)
        self.layout.setSpacing(0)

        # Create SourceList widget
        self.source_list = SourceList()
        self.source_list.itemSelectionChanged.connect(self.on_source_changed)

        # Create widgets
        self.view_holder = QWidget()
        self.view_holder.setObjectName('view_holder')
        self.view_layout = QVBoxLayout()
        self.view_holder.setLayout(self.view_layout)
        self.view_layout.setContentsMargins(0, 0, 0, 0)
        self.view_layout.setSpacing(0)
        self.empty_conversation_view = EmptyConversationView()
        self.view_layout.addWidget(self.empty_conversation_view)

        # Add widgets to layout
        self.layout.addWidget(self.source_list)
        self.layout.addWidget(self.view_holder)

        # Note: We should not delete SourceConversationWrapper when its source is unselected. This
        # is a temporary solution to keep copies of our objects since we do delete them.
        self.source_conversations = {}  # type: Dict[Source, SourceConversationWrapper]

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
        if len(sources) == 0:
            self.empty_conversation_view.show_no_sources_message()
            self.empty_conversation_view.show()
        else:
            self.empty_conversation_view.show_no_source_selected_message()
            self.empty_conversation_view.show()

        self.source_list.update(sources)

    def on_source_changed(self):
        """
        Show conversation for the currently-selected source if it hasn't been deleted. If the
        current source no longer exists, clear the conversation for that source.
        """
        source = self.source_list.get_current_source()

        if source:
            self.controller.session.refresh(source)
            # Try to get the SourceConversationWrapper from the persistent dict,
            # else we create it.
            try:
                conversation_wrapper = self.source_conversations[source]

                # Redraw the conversation view such that new messages, replies, files appear.
                conversation_wrapper.conversation_view.update_conversation(source.collection)
            except KeyError:
                conversation_wrapper = SourceConversationWrapper(source, self.controller)
                self.source_conversations[source] = conversation_wrapper

            self.set_conversation(conversation_wrapper)
        else:
            self.clear_conversation()

    def set_conversation(self, widget):
        """
        Update the view holder to contain the referenced widget.
        """
        old_widget = self.view_layout.takeAt(0)

        if old_widget and old_widget.widget():
            old_widget.widget().hide()

        self.empty_conversation_view.hide()
        self.view_layout.addWidget(widget)
        widget.show()

    def clear_conversation(self):
        while self.view_layout.count():
            child = self.view_layout.takeAt(0)
            if child.widget():
                child.widget().deleteLater()


class EmptyConversationView(QWidget):

    CSS = '''
    #content {
        font-family: Montserrat;
        font-weight: 400;
        font-size: 35px;
        color: #a5b3e9;
        qproperty-alignment: AlignLeft;
    }
    '''

    def __init__(self):
        super().__init__()

        # Set id and styles
        self.setObjectName('view')
        self.setStyleSheet(self.CSS)

        # Set layout
        layout = QHBoxLayout(self)
        self.setLayout(layout)

        # Set margins and spacing
        layout.setContentsMargins(0, 100, 0, 0)
        layout.setSpacing(0)

        # Create widgets
        self.content = QLabel(self)
        self.content.setObjectName('content')
        self.content.setWordWrap(True)
        content_layout = QVBoxLayout()
        content_layout.addStretch(1)
        content_layout.addWidget(self.content, 8)
        content_layout.addStretch(1)

        # Add widgets
        layout.addStretch(1)
        layout.addWidget(self.content, 5)
        layout.addStretch(1)

    def show_no_sources_message(self):
        self.content.setText(
            'Nothing to see just yet!\n\n'
            'Source submissions will be listed to the left, once downloaded and decrypted.\n\n'
            'This is where you will read messages, reply to sources, and work with files.\n\n')

    def show_no_source_selected_message(self):
        self.content.setText(
            'Select a source from the list, to:\n\n'
            '• Read a conversation\n'
            '• View or retrieve files\n'
            '• Send a response\n')


class SourceList(QListWidget):
    """
    Displays the list of sources.
    """

    CSS = '''
    QListView {
        border: none;
        show-decoration-selected: 0;
        border-right: 3px solid #f3f5f9;
    }
    QListView::item:selected {
        background-color: #f3f5f9;
    }
    QListView::item:hover{
        border: 500px solid #f9f9f9;
    }
    '''

    def __init__(self):
        super().__init__()

        # Set id and styles.
        self.setObjectName('sourcelist')
        self.setStyleSheet(self.CSS)
        self.setFixedWidth(445)
        self.setUniformItemSizes(True)

        # Set layout.
        layout = QVBoxLayout(self)
        self.setLayout(layout)

        # To hold references to SourceWidget instances indexed by source UUID.
        self.source_widgets = {}

    def setup(self, controller):
        self.controller = controller
        self.controller.reply_succeeded.connect(self.set_snippet)
        self.controller.message_ready.connect(self.set_snippet)
        self.controller.reply_ready.connect(self.set_snippet)
        self.controller.file_ready.connect(self.set_snippet)
        self.controller.file_missing.connect(self.set_snippet)

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
            self.source_widgets[source.uuid] = new_source

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

    def set_snippet(self, source_uuid, message_uuid, content):
        """
        Given a UUID of a source, if the referenced message is the latest
        message, then update the source's preview snippet to the referenced
        content.
        """
        source_widget = self.source_widgets.get(source_uuid)
        if source_widget:
            source_widget.set_snippet(source_uuid, message_uuid, content)


class SourceWidget(QWidget):
    """
    Used to display summary information about a source in the list view.

    -----------------------------------------------------------------------------
    |                                                                           |
    |     -----------------------------------------------------------------     |
    |     |                                                               |     |
    |     |                                                               |     |
    |     | ------------- ---------------------------- ------------------ |     |
    |     | | ------    | | ------                   | |    ----------- | |     |
    |     | | |star|    | | |name|                   | |    |paperclip| | |     |
    |     | | ------    | | ------                   | |    ----------- | |     |
    |     | |           | | ---------                | |    ----------- | |     |
    |     | |           | | |preview|                | |    |timestamp| | |     |
    |     | |           | | ---------                | |    ----------- | |     |
    |     | |           | |                          | |                | |     |
    |     | |    gutter | |                  summary | |       metadata | |     |
    |     | ------------- ---------------------------- ------------------ |     |
    |     |                                                               |     |
    |     |                                                 source_widget |     |
    |     -----------------------------------------------------------------     |
    |                                                              SourceWidget |
    -----------------------------------------------------------------------------
    """

    CSS = '''
    QWidget#source_widget {
        border-bottom: 1px solid #9b9b9b;
    }
    QWidget#gutter {
        min-width: 40px;
        max-width: 40px;
    }
    QWidget#metadata {
        max-width: 60px;
    }
    QLabel#preview {
        font-family: 'Source Sans Pro';
        font-weight: 400;
        font-size: 13px;
        color: #383838;
    }
    QLabel#source_name {
        font-family: 'Montserrat';
        font-weight: 500;
        font-size: 13px;
        color: #383838;
    }
    QLabel#timestamp {
        font-family: 'Montserrat';
        font-weight: 500;
        font-size: 13px;
        color: #383838;
    }
    '''

    SIDE_MARGIN = 10
    SOURCE_WIDGET_VERTICAL_MARGIN = 10
    PREVIEW_WIDTH = 312
    PREVIEW_HEIGHT = 60

    def __init__(self, source: Source):
        super().__init__()

        # Store source
        self.source = source

        # Set styles
        self.setStyleSheet(self.CSS)

        # Set layout
        layout = QHBoxLayout(self)
        self.setLayout(layout)

        # Set cursor.
        self.setCursor(QCursor(Qt.PointingHandCursor))

        # Remove margins and spacing
        layout.setContentsMargins(self.SIDE_MARGIN, 0, self.SIDE_MARGIN, 0)
        layout.setSpacing(0)

        # Set up gutter
        self.gutter = QWidget()
        self.gutter.setObjectName('gutter')
        gutter_layout = QVBoxLayout(self.gutter)
        gutter_layout.setContentsMargins(0, 0, 0, 0)
        gutter_layout.setSpacing(0)
        self.star = StarToggleButton(self.source)
        gutter_layout.addWidget(self.star)
        gutter_layout.addStretch()

        # Set up summary
        self.summary = QWidget()
        self.summary.setObjectName('summary')
        summary_layout = QVBoxLayout(self.summary)
        summary_layout.setContentsMargins(0, 0, 0, 0)
        summary_layout.setSpacing(0)
        self.name = QLabel()
        self.name.setObjectName('source_name')
        self.preview = SecureQLabel()
        self.preview.setObjectName('preview')
        self.preview.setFixedSize(QSize(self.PREVIEW_WIDTH, self.PREVIEW_HEIGHT))
        self.preview.setWordWrap(True)
        summary_layout.addWidget(self.name)
        summary_layout.addWidget(self.preview)

        # Set up metadata
        self.metadata = QWidget()
        self.metadata.setObjectName('metadata')
        metadata_layout = QVBoxLayout(self.metadata)
        metadata_layout.setContentsMargins(0, 0, 0, 0)
        metadata_layout.setSpacing(0)
        self.paperclip = SvgLabel('paperclip.svg', QSize(18, 18))  # Set to size provided in the svg
        self.paperclip.setObjectName('paperclip')
        self.paperclip.setFixedSize(QSize(22, 22))
        self.timestamp = QLabel()
        self.timestamp.setObjectName('timestamp')
        metadata_layout.addWidget(self.paperclip, 0, Qt.AlignRight)
        metadata_layout.addWidget(self.timestamp, 0, Qt.AlignRight)
        metadata_layout.addStretch()

        # Set up a source_widget
        self.source_widget = QWidget()
        self.source_widget.setObjectName('source_widget')
        source_widget_layout = QHBoxLayout(self.source_widget)
        source_widget_layout.setContentsMargins(
            0, self.SOURCE_WIDGET_VERTICAL_MARGIN, 0, self.SOURCE_WIDGET_VERTICAL_MARGIN)
        source_widget_layout.setSpacing(0)
        source_widget_layout.addWidget(self.gutter)
        source_widget_layout.addWidget(self.summary)
        source_widget_layout.addWidget(self.metadata)

        # Add widgets to main layout
        layout.addWidget(self.source_widget)

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
        self.timestamp.setText(_(arrow.get(self.source.last_updated).format('DD MMM')))
        self.name.setText(self.source.journalist_designation)
        self.set_snippet(self.source.uuid)
        if self.source.document_count == 0:
            self.paperclip.hide()

    def set_snippet(self, source, uuid=None, content=None):
        """
        Update the preview snippet only if the new message is for the
        referenced source and there's a source collection. If a uuid and
        content are passed then use these, otherwise default to whatever the
        latest item in the conversation might be.
        """
        if source == self.source.uuid and self.source.collection:
            msg = self.source.collection[-1]
            if uuid and uuid == msg.uuid and content:
                msg_text = content
            else:
                msg_text = str(msg)
            if len(msg_text) > 120:
                msg_text = msg_text[:120] + "..."
            self.preview.setText(msg_text)

    def delete_source(self, event):
        if self.controller.api is None:
            self.controller.on_action_requiring_login()
            return
        else:
            messagebox = DeleteSourceMessageBox(self.source, self.controller)
            messagebox.launch()


class StarToggleButton(SvgToggleButton):
    """
    A button that shows whether or not a source is starred
    """

    css = '''
    #star_button {
        border: none;
    }
    #star_button:hover {
        border: 4px solid #D3D8EA;
        border-radius: 8px;
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
        self.controller.update_star(self.source, self.on_update)

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

    def on_update(self, result):
        """
        The result is a uuid for the source and boolean flag for the new state
        of the star.
        """
        enabled = result[1]
        self.source.is_starred = enabled
        self.controller.update_sources()
        self.setChecked(enabled)


class DeleteSourceMessageBox:
    """Use this to display operation details and confirm user choice."""

    def __init__(self, source, controller):
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
            None, "", _(message), QMessageBox.Cancel | QMessageBox.Yes, QMessageBox.Cancel)

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


class LoginOfflineLink(QLabel):
    """
    A button that logs the user in in offline mode.
    """

    clicked = pyqtSignal()

    CSS = '''
    #offline_mode {
        border: none;
        color: #fff;
        text-decoration: underline;
    }
    '''

    def __init__(self):
        # Add svg images to button
        super().__init__()

        # Set css id
        self.setObjectName('offline_mode')

        # Set styles
        self.setStyleSheet(self.CSS)
        self.setFixedSize(QSize(120, 22))

        self.setText(_('USE OFFLINE'))

    def mouseReleaseEvent(self, event):
        self.clicked.emit()


class SignInButton(QPushButton):
    """
    A button that logs the user into application when clicked.
    """

    CSS = '''
    #login {
        border: none;
        background-color: #05edfe;
        font-family: 'Montserrat';
        font-weight: 600;
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
        self.setFixedWidth(140)

        # Set cursor.
        self.setCursor(QCursor(Qt.PointingHandCursor))

        # Set drop shadow effect
        effect = QGraphicsDropShadowEffect(self)
        effect.setOffset(0, 1)
        effect.setBlurRadius(8)
        effect.setColor(QColor('#aa000000'))
        self.setGraphicsEffect(effect)
        self.update()


class LoginErrorBar(QWidget):
    """
    A bar widget for displaying messages about login errors to the user.
    """

    CSS = '''
    QWidget {
        background-color: #ce0083;
    }
    #error_icon {
        color: #fff;
    }
    #error_status_bar {
        font-family: 'Montserrat';
        font-weight: 500;
        font-size: 12px;
        color: #fff;
    }
    '''

    def __init__(self):
        super().__init__()

        self.setObjectName('error_bar')

        # Set styles
        self.setStyleSheet(self.CSS)

        # Set layout
        layout = QHBoxLayout(self)
        self.setLayout(layout)

        # Remove margins and spacing
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Set size policy
        retain_space = self.sizePolicy()
        retain_space.setRetainSizeWhenHidden(True)
        self.setSizePolicy(retain_space)

        # Error icon
        self.error_icon = SvgLabel('error_icon_white.svg', svg_size=QSize(18, 18))
        self.error_icon.setObjectName('error_icon')
        self.error_icon.setFixedWidth(42)

        # Error status bar
        self.error_status_bar = QLabel()
        self.error_status_bar.setObjectName('error_status_bar')
        self.setFixedHeight(42)

        # Create space ths size of the error icon to keep the error message centered
        spacer1 = QWidget()
        spacer2 = QWidget()

        # Add widgets to layout
        layout.addWidget(spacer1)
        layout.addWidget(self.error_icon)
        layout.addWidget(self.error_status_bar)
        layout.addWidget(spacer2)

    def set_message(self, message):
        self.show()
        self.error_status_bar.setText(message)

    def clear_message(self):
        self.error_status_bar.setText('')
        self.hide()


class PasswordEdit(QLineEdit):
    """
    A LineEdit with icons to show/hide password entries
    """
    CSS = '''QLineEdit {
        border-radius: 0px;
        height: 30px;
        margin: 0px 0px 0px 0px;
    }
    '''

    def __init__(self, parent):
        self.parent = parent
        super().__init__(self.parent)

        # Set styles
        self.setStyleSheet(self.CSS)

        self.visibleIcon = load_icon("eye_visible.svg")
        self.hiddenIcon = load_icon("eye_hidden.svg")

        self.setEchoMode(QLineEdit.Password)
        self.togglepasswordAction = self.addAction(self.hiddenIcon, QLineEdit.TrailingPosition)
        self.togglepasswordAction.triggered.connect(self.on_toggle_password_Action)
        self.password_shown = False

    def on_toggle_password_Action(self):
        if not self.password_shown:
            self.setEchoMode(QLineEdit.Normal)
            self.password_shown = True
            self.togglepasswordAction.setIcon(self.visibleIcon)
        else:
            self.setEchoMode(QLineEdit.Password)
            self.password_shown = False
            self.togglepasswordAction.setIcon(self.hiddenIcon)


class LoginDialog(QDialog):
    """
    A dialog to display the login form.
    """

    CSS = '''
    #login_form QLabel {
        color: #fff;
        font-family: 'Montserrat';
        font-weight: 500;
        font-size: 13px;
    }
    #login_form QLineEdit {
        border-radius: 0px;
        height: 30px;
        margin: 0px 0px 0px 0px;
    }
    '''

    MIN_PASSWORD_LEN = 14  # Journalist.MIN_PASSWORD_LEN on server
    MAX_PASSWORD_LEN = 128  # Journalist.MAX_PASSWORD_LEN on server
    MIN_JOURNALIST_USERNAME = 3  # Journalist.MIN_USERNAME_LEN on server

    def __init__(self, parent):
        self.parent = parent
        super().__init__(self.parent)

        # Set css id
        self.setObjectName('login_dialog')

        # Set styles
        self.setStyleSheet(self.CSS)

        # Set layout
        layout = QVBoxLayout(self)
        self.setLayout(layout)

        # Set margins and spacing
        layout.setContentsMargins(0, 274, 0, 20)
        layout.setSpacing(0)

        # Set background
        self.setAutoFillBackground(True)
        palette = QPalette()
        palette.setBrush(QPalette.Background, QBrush(load_image('login_bg.svg')))
        self.setPalette(palette)
        self.setFixedSize(QSize(596, 671))  # Set to size provided in the login_bg.svg file
        self.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)

        # Create error bar
        self.error_bar = LoginErrorBar()

        # Create form widget
        form = QWidget()

        form.setObjectName('login_form')

        form_layout = QVBoxLayout()
        form.setLayout(form_layout)

        form_layout.setContentsMargins(80, 0, 80, 0)
        form_layout.setSpacing(8)

        self.username_label = QLabel(_('Username'))
        self.username_field = QLineEdit()

        self.password_label = QLabel(_('Passphrase'))
        self.password_field = PasswordEdit(self)

        self.tfa_label = QLabel(_('Two-Factor Code'))
        self.tfa_field = QLineEdit()

        buttons = QWidget()
        buttons_layout = QHBoxLayout()
        buttons.setLayout(buttons_layout)
        buttons_layout.setContentsMargins(0, 20, 0, 0)
        self.submit = SignInButton()
        self.submit.clicked.connect(self.validate)
        self.offline_mode = LoginOfflineLink()
        buttons_layout.addWidget(self.offline_mode)
        buttons_layout.addStretch()
        buttons_layout.addWidget(self.submit)

        form_layout.addWidget(self.username_label)
        form_layout.addWidget(self.username_field)
        form_layout.addWidget(QWidget(self))
        form_layout.addWidget(self.password_label)
        form_layout.addWidget(self.password_field)
        form_layout.addWidget(QWidget(self))
        form_layout.addWidget(self.tfa_label)
        form_layout.addWidget(self.tfa_field)
        form_layout.addWidget(buttons)

        # Create widget to display application name and version
        application_version = QWidget()
        application_version_layout = QHBoxLayout()
        application_version.setLayout(application_version_layout)

        # Add widgets
        layout.addWidget(self.error_bar)
        layout.addStretch()
        layout.addWidget(form)
        layout.addStretch()
        layout.addWidget(application_version)

    def closeEvent(self, event):
        """
        Only exit the application when the main window is not visible.
        """
        if not self.parent.isVisible():
            sys.exit(0)

    def keyPressEvent(self, event):
        """
        Cutomize keyboard behavior in the login dialog.

        - [Esc] should not close the dialog
        - [Enter] or [Return] should attempt to submit the form
        """
        if event.key() == Qt.Key_Escape:
            event.ignore()

        if event.key() == Qt.Key_Enter or event.key() == Qt.Key_Return:
            self.validate()

    def setup(self, controller):
        self.controller = controller
        self.offline_mode.clicked.connect(self.controller.login_offline_mode)

    def reset(self):
        """
        Resets the login form to the default state.
        """
        self.username_field.setText('')
        self.username_field.setFocus()
        self.password_field.setText('')
        self.tfa_field.setText('')
        self.setDisabled(False)
        self.error_bar.clear_message()

    def error(self, message):
        """
        Ensures the passed in message is displayed as an error message.
        """
        self.setDisabled(False)
        self.error_bar.set_message(html.escape(message))

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
                self.error(_('Please use only numerals for the two-factor code.'))
                return

            self.controller.login(username, password, tfa_token)
        else:
            self.setDisabled(False)
            self.error(_('Please enter a username, password and '
                         'two-factor code.'))


class SpeechBubble(QWidget):
    """
    Represents a speech bubble that's part of a conversation between a source
    and journalist.
    """

    CSS = '''
    #speech_bubble {
        min-width: 540px;
        max-width: 540px;
        background-color: #fff;
        padding: 16px;
    }
    #message {
        min-width: 540px;
        max-width: 540px;
        font-family: 'Source Sans Pro';
        font-weight: 400;
        font-size: 15px;
        background-color: #fff;
        padding: 16px;
    }
    #color_bar {
        min-height: 5px;
        max-height: 5px;
        background-color: #102781;
        border: 0px;
        min-width: 590px;
        max-width: 590px;
    }
    '''

    TOP_MARGIN = 28
    BOTTOM_MARGIN = 10

    def __init__(self, message_id: str, text: str, update_signal, index: int) -> None:
        super().__init__()
        self.message_id = message_id
        self.index = index

        # Set styles
        self.setObjectName('speech_bubble')
        self.setStyleSheet(self.CSS)
        self.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)

        # Set layout
        layout = QVBoxLayout()
        self.setLayout(layout)

        # Set margins and spacing
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Message box
        self.message = SecureQLabel(text)
        self.message.setObjectName('message')
        self.message.setWordWrap(True)

        # Color bar
        self.color_bar = QWidget()
        self.color_bar.setObjectName('color_bar')

        # Speech bubble
        speech_bubble = QWidget()
        speech_bubble_layout = QVBoxLayout()
        speech_bubble.setLayout(speech_bubble_layout)
        speech_bubble_layout.addWidget(self.message)
        speech_bubble_layout.addWidget(self.color_bar)
        speech_bubble_layout.setSpacing(0)

        # Bubble area includes speech bubble plus error message if there is an error
        bubble_area = QWidget()
        bubble_area.setLayoutDirection(Qt.RightToLeft)
        self.bubble_area_layout = QHBoxLayout()
        self.bubble_area_layout.setContentsMargins(0, self.TOP_MARGIN, 0, self.BOTTOM_MARGIN)
        bubble_area.setLayout(self.bubble_area_layout)
        self.bubble_area_layout.addWidget(speech_bubble)

        # Add widget to layout
        layout.addWidget(bubble_area)

        # Connect signals to slots
        update_signal.connect(self._update_text)

    @pyqtSlot(str, str, str)
    def _update_text(self, source_id: str, message_id: str, text: str) -> None:
        """
        Conditionally update this SpeechBubble's text if and only if the message_id of the emitted
        signal matches the message_id of this speech bubble.
        """
        if message_id == self.message_id:
            self.message.setText(text)


class MessageWidget(SpeechBubble):
    """
    Represents an incoming message from the source.
    """

    def __init__(self, message_id: str, message: str, update_signal, index: int) -> None:
        super().__init__(message_id, message, update_signal, index)


class ReplyWidget(SpeechBubble):
    """
    Represents a reply to a source.
    """

    CSS_REPLY_FAILED = '''
    #message {
        min-width: 540px;
        max-width: 540px;
        font-family: 'Source Sans Pro';
        font-weight: 400;
        font-size: 15px;
        background-color: #fff;
        color: #3b3b3b;
        padding: 16px;
    }
    #color_bar {
        min-height: 5px;
        max-height: 5px;
        background-color: #ff3366;
        border: 0px;
    }
    #error_message {
        font-family: 'Source Sans Pro';
        font-weight: 500;
        font-size: 13px;
        color: #ff3366;
    }
    '''

    CSS_REPLY_SUCCEEDED = '''
    #message {
        min-width: 540px;
        max-width: 540px;
        font-family: 'Source Sans Pro';
        font-weight: 400;
        font-size: 15px;
        background-color: #fff;
        color: #3b3b3b;
        padding: 16px;
    }
    #color_bar {
        min-height: 5px;
        max-height: 5px;
        background-color: #0065db;
        border: 0px;
    }
    '''

    # Custom pending CSS styling simulates the effect of opacity which is only
    # supported by tooltips for QSS.
    CSS_REPLY_PENDING = '''
    #message {
        min-width: 540px;
        max-width: 540px;
        font-family: 'Source Sans Pro';
        font-weight: 400;
        font-size: 15px;
        color: #A9AAAD;
        background-color: #F7F8FC;
        padding: 16px;
    }
    #color_bar {
        min-height: 5px;
        max-height: 5px;
        background-color: #0065db;
        border: 0px;
    }
    '''

    def __init__(
        self,
        message_id: str,
        message: str,
        reply_status: str,
        update_signal,
        message_succeeded_signal,
        message_failed_signal,
        index: int,
    ) -> None:
        super().__init__(message_id, message, update_signal, index)
        self.message_id = message_id

        error_icon = SvgLabel('error_icon.svg', svg_size=QSize(12, 12))
        error_icon.setObjectName('error_icon')  # Set css id
        error_icon.setFixedWidth(12)
        error_message = SecureQLabel('Failed to send')
        error_message.setObjectName('error_message')

        self.error = QWidget()
        error_layout = QHBoxLayout()
        error_layout.setContentsMargins(0, 0, 0, 0)
        error_layout.setSpacing(4)
        self.error.setLayout(error_layout)
        error_layout.addWidget(error_message)
        error_layout.addWidget(error_icon)

        self.error.hide()
        self.bubble_area_layout.addWidget(self.error)

        message_succeeded_signal.connect(self._on_reply_success)
        message_failed_signal.connect(self._on_reply_failure)

        # Set styles
        self._set_reply_state(reply_status)

    def _set_reply_state(self, status: str) -> None:
        if status == 'SUCCEEDED':
            self.setStyleSheet(self.CSS_REPLY_SUCCEEDED)
            self.error.hide()
        elif status == 'FAILED':
            self.setStyleSheet(self.CSS_REPLY_FAILED)
            self.error.show()
        elif status == 'PENDING':
            self.setStyleSheet(self.CSS_REPLY_PENDING)

    @pyqtSlot(str, str, str)
    def _on_reply_success(self, source_id: str, message_id: str, content: str) -> None:
        """
        Conditionally update this ReplyWidget's state if and only if the message_id of the emitted
        signal matches the message_id of this widget.
        """
        if message_id == self.message_id:
            self._set_reply_state('SUCCEEDED')

    @pyqtSlot(str)
    def _on_reply_failure(self, message_id: str) -> None:
        """
        Conditionally update this ReplyWidget's state if and only if the message_id of the emitted
        signal matches the message_id of this widget.
        """
        if message_id == self.message_id:
            self._set_reply_state('FAILED')


class FileWidget(QWidget):
    """
    Represents a file.
    """

    CSS = '''
    #file_widget {
        min-width: 540px;
        max-width: 540px;
        padding: 16px;
    }
    #file_options {
        min-width: 137px;
    }
    QPushButton#export_print {
        border: none;
        padding: 0px 8px;
        font-family: 'Source Sans Pro';
        font-weight: 500;
        font-size: 13px;
        color: #2A319D;
    }
    QPushButton#export_print:hover {
        color: #05a6fe;
    }
    QPushButton#download_button {
        border: none;
        font-family: 'Source Sans Pro';
        font-weight: 600;
        font-size: 13px;
        color: #2a319d;
    }
    QLabel#file_name {
        min-width: 129px;
        padding-right: 8px;
        font-family: 'Source Sans Pro';
        font-weight: 700;
        font-size: 13px;
        color: #2a319d;
    }
    QLabel#no_file_name {
        padding-right: 8px;
        font-family: 'Source Sans Pro';
        font-weight: 300;
        font-size: 13px;
        color: #a5b3e9;
    }
    QLabel#file_size {
        min-width: 48px;
        max-width: 48px;
        font-family: 'Source Sans Pro';
        font-weight: 400;
        font-size: 14px;
        color: #2a319d;
    }
    QWidget#horizontal_line {
        min-height: 2px;
        max-height: 2px;
        background-color: rgba(211, 216, 234, 0.45);
        padding-left: 8px;
        padding-right: 8px;
    }
    '''

    VERTICAL_MARGIN = 10
    FILE_FONT_SPACING = 2
    FILE_OPTIONS_FONT_SPACING = 1.6

    def __init__(
        self,
        file_uuid: str,
        controller: Controller,
        file_ready_signal: pyqtBoundSignal,
        file_missing: pyqtBoundSignal,
        index: int,
    ) -> None:
        """
        Given some text and a reference to the controller, make something to display a file.
        """
        super().__init__()

        self.controller = controller
        self.file = self.controller.get_file(file_uuid)
        self.index = index

        # Set styles
        self.setObjectName('file_widget')
        self.setStyleSheet(self.CSS)
        file_description_font = QFont()
        file_description_font.setLetterSpacing(QFont.AbsoluteSpacing, self.FILE_FONT_SPACING)
        self.file_buttons_font = QFont()
        self.file_buttons_font.setLetterSpacing(
            QFont.AbsoluteSpacing, self.FILE_OPTIONS_FONT_SPACING)

        # Set layout
        layout = QHBoxLayout()
        self.setLayout(layout)

        # Set margins and spacing
        layout.setContentsMargins(0, self.VERTICAL_MARGIN, 0, self.VERTICAL_MARGIN)
        layout.setSpacing(0)
        self.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)

        # File options: download, export, print
        self.file_options = QWidget()
        self.file_options.setObjectName('file_options')
        file_options_layout = QHBoxLayout()
        self.file_options.setLayout(file_options_layout)
        file_options_layout.setContentsMargins(0, 0, 0, 0)
        file_options_layout.setSpacing(0)
        file_options_layout.setAlignment(Qt.AlignLeft)
        self.download_button = QPushButton(_(' DOWNLOAD'))
        self.download_button.setObjectName('download_button')
        self.download_button.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)
        self.download_button.setIcon(load_icon('download_file.svg'))
        self.download_button.setFont(self.file_buttons_font)
        self.download_animation = load_movie("download_file.gif")
        self.export_button = QPushButton(_('EXPORT'))
        self.export_button.setObjectName('export_print')
        self.export_button.setFont(self.file_buttons_font)
        self.middot = QLabel("·")
        self.print_button = QPushButton(_('PRINT'))
        self.print_button.setObjectName('export_print')
        self.print_button.setFont(self.file_buttons_font)
        file_options_layout.addWidget(self.download_button)
        file_options_layout.addWidget(self.export_button)
        file_options_layout.addWidget(self.middot)
        file_options_layout.addWidget(self.print_button)

        self.download_button.installEventFilter(self)
        self.export_button.clicked.connect(self._on_export_clicked)
        self.print_button.clicked.connect(self._on_print_clicked)

        # File name or default string
        self.file_name = SecureQLabel(self.file.filename)
        self.file_name.setObjectName('file_name')
        self.file_name.installEventFilter(self)
        self.no_file_name = SecureQLabel('ENCRYPTED FILE ON SERVER')
        self.no_file_name.setObjectName('no_file_name')
        self.no_file_name.setFont(file_description_font)

        # Line between file name and file size
        horizontal_line = QWidget()
        horizontal_line.setObjectName('horizontal_line')
        horizontal_line.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        # File size
        self.file_size = SecureQLabel(humanize_filesize(self.file.size))
        self.file_size.setObjectName('file_size')
        self.file_size.setAlignment(Qt.AlignRight)

        # Decide what to show or hide based on whether or not the file's been downloaded
        if self.file.is_downloaded:
            self.download_button.hide()
            self.no_file_name.hide()
            self.export_button.show()
            self.middot.show()
            self.print_button.show()
            self.file_name.show()
        else:
            self.export_button.hide()
            self.middot.hide()
            self.print_button.hide()
            self.file_name.hide()
            self.download_button.show()
            self.no_file_name.show()

        # Add widgets
        layout.addWidget(self.file_options)
        layout.addWidget(self.file_name)
        layout.addWidget(self.no_file_name)
        layout.addWidget(horizontal_line)
        layout.addWidget(self.file_size)

        # Connect signals to slots
        file_ready_signal.connect(self._on_file_downloaded, type=Qt.QueuedConnection)
        file_missing.connect(self._on_file_missing, type=Qt.QueuedConnection)

    def eventFilter(self, obj, event):
        if event.type() == QEvent.MouseButtonPress:
            if event.button() == Qt.LeftButton:
                self._on_left_click()
        return QObject.event(obj, event)

    @pyqtSlot(str, str, str)
    def _on_file_downloaded(self, source_uuid: str, file_uuid: str, filename: str) -> None:
        if file_uuid == self.file.uuid:
            self.file = self.controller.get_file(self.file.uuid)
            if self.file.is_downloaded:
                self.file_name.setText(self.file.filename)
                self.download_button.hide()
                self.no_file_name.hide()
                self.export_button.show()
                self.middot.show()
                self.print_button.show()
                self.file_name.show()

    @pyqtSlot(str, str, str)
    def _on_file_missing(self, source_uuid: str, file_uuid: str, filename: str) -> None:
        if file_uuid == self.file.uuid:
            self.file = self.controller.get_file(self.file.uuid)
            if not self.file.is_downloaded:
                self.download_animation.stop()
                self.download_button.setText(_('DOWNLOAD'))
                self.download_button.setIcon(load_icon('download_file.svg'))
                self.download_button.setStyleSheet('color: #2a319d')
                self.download_button.setFont(self.file_buttons_font)
                self.download_button.show()
                self.no_file_name.hide()
                self.export_button.hide()
                self.middot.hide()
                self.print_button.hide()
                self.file_name.hide()
                self.no_file_name.show()

    @pyqtSlot()
    def _on_export_clicked(self):
        """
        Called when the export button is clicked.
        """
        if not self.controller.downloaded_file_exists(self.file):
            return

        dialog = ExportDialog(self.controller, self.file.uuid,
                              self.file.filename)
        dialog.show()
        dialog.export()
        dialog.exec()

    @pyqtSlot()
    def _on_print_clicked(self):
        """
        Called when the print button is clicked.
        """
        if not self.controller.downloaded_file_exists(self.file):
            return

        dialog = PrintDialog(self.controller, self.file.uuid)
        dialog.show()
        dialog.print()
        dialog.exec()

    def _on_left_click(self):
        """
        Handle a completed click via the program logic. The download state
        of the file distinguishes which function in the logic layer to call.
        """
        # update state
        self.file = self.controller.get_file(self.file.uuid)

        if self.file.is_downloaded:
            # Open the already downloaded file.
            self.controller.on_file_open(self.file)
        else:
            if self.controller.api:
                # Indicate in downloading state... but only after 0.3 seconds (i.e.
                # this is taking a noticable amount of time to complete).
                QTimer.singleShot(300, self.start_button_animation)
            # Download the file.
            self.controller.on_submission_download(File, self.file.uuid)

    def start_button_animation(self):
        """
        Update the download button to the animated "downloading" state.
        """
        self.download_animation.frameChanged.connect(self.set_button_animation_frame)
        self.download_animation.start()
        self.download_button.setText(_(" DOWNLOADING "))
        self.download_button.setStyleSheet("color: #05a6fe")

    def set_button_animation_frame(self, frame_number):
        """
        Sets the download button's icon to the current frame of the spinner
        animation.
        """
        self.download_button.setIcon(QIcon(self.download_animation.currentPixmap()))


class PrintDialog(QDialog):

    CSS_FOR_DIALOG_WITH_ERROR = '''
    #print_dialog {
        min-width: 830;
        min-height: 430;
        border: 1px solid #2a319d;
    }
    '''

    CSS = '''
    #print_dialog {
        min-width: 400;
        max-width: 400;
        min-height: 200;
        max-height: 200;
    }
    '''

    def __init__(self, controller, file_uuid):
        super().__init__()

        self.controller = controller
        self.file_uuid = file_uuid

        self.setObjectName('print_dialog')
        self.setStyleSheet(self.CSS)
        self.setWindowFlags(Qt.Popup)
        self.setWindowModality(Qt.WindowModal)

        layout = QVBoxLayout(self)
        self.setLayout(layout)

        # Opening VM message
        self.starting_message = SecureQLabel(_('Preparing print...'))
        self.starting_message.setWordWrap(True)

        # Widget to show error messages that occur during print
        self.generic_error = QWidget()
        self.generic_error.setObjectName('generic_error')
        generic_error_layout = QHBoxLayout()
        self.generic_error.setLayout(generic_error_layout)
        self.error_status_code = SecureQLabel()
        generic_error_message = SecureQLabel(_('See your administrator for help.'))
        generic_error_message.setWordWrap(True)
        generic_error_layout.addWidget(self.error_status_code)
        generic_error_layout.addWidget(generic_error_message)

        # Insert USB Device Form
        self.insert_usb_form = QWidget()
        self.insert_usb_form.setObjectName('insert_usb_form')
        usb_form_layout = QVBoxLayout()
        self.insert_usb_form.setLayout(usb_form_layout)
        self.usb_error_message = SecureQLabel(_(
            'Please try reconnecting your printer, or see your administrator for help.'))
        self.usb_error_message.setWordWrap(True)
        usb_instructions = SecureQLabel(_('Please connect your printer to a USB port.'))
        usb_instructions.setWordWrap(True)
        buttons = QWidget()
        buttons_layout = QHBoxLayout()
        buttons.setLayout(buttons_layout)
        cancel_button = QPushButton(_('CANCEL'))
        retry_button = QPushButton(_('CONTINUE'))
        buttons_layout.addWidget(cancel_button)
        buttons_layout.addWidget(retry_button)
        usb_form_layout.addWidget(self.usb_error_message)
        usb_form_layout.addWidget(usb_instructions)
        usb_form_layout.addWidget(buttons, alignment=Qt.AlignRight)

        # Printing message
        self.printing_message = SecureQLabel(_('Printing...'))
        self.printing_message.setWordWrap(True)

        layout.addWidget(self.starting_message)
        layout.addWidget(self.printing_message)
        layout.addWidget(self.generic_error)
        layout.addWidget(self.insert_usb_form)

        self.starting_message.show()
        self.printing_message.hide()
        self.generic_error.hide()
        self.insert_usb_form.hide()

        cancel_button.clicked.connect(self.close)
        retry_button.clicked.connect(self._on_retry_button_clicked)

        self.controller.export.print_call_failure.connect(
            self._on_print_failure, type=Qt.QueuedConnection)
        self.controller.export.print_call_success.connect(
            self._on_print_success, type=Qt.QueuedConnection)

    def print(self):
        self.starting_message.hide()
        self.printing_message.show()
        self.generic_error.hide()
        self.insert_usb_form.hide()
        self.controller.print_file(self.file_uuid)

    @pyqtSlot()
    def _on_retry_button_clicked(self):
        self.print()

    @pyqtSlot()
    def _on_print_success(self):
        self.close()

    @pyqtSlot(object)
    def _on_print_failure(self, error: ExportError):
        self._update(error.status)

    def _update(self, status):
        logger.debug('updating status... ')
        if status == ExportStatus.PRINTER_NOT_FOUND.value:
            self._request_to_insert_usb_device()
        else:
            self.error_status_code.setText(_(status))
            self.starting_message.hide()
            self.printing_message.hide()
            self.generic_error.show()
            self.insert_usb_form.hide()

    def _request_to_insert_usb_device(self):
        self.starting_message.hide()
        self.printing_message.hide()
        self.generic_error.hide()
        self.insert_usb_form.show()


class ExportDialog(QDialog):

    CSS = '''
    #export_dialog {
        min-width: 830;
        min-height: 330;
        border: 1px solid #2a319d;
    }
    '''

    CSS_FOR_DIALOG_WITH_ERROR = '''
    #export_dialog {
        min-width: 830;
        min-height: 430;
        border: 1px solid #2a319d;
    }
    '''

    CSS = '''
    #export_dialog {
        min-width: 400;
        max-width: 400;
        min-height: 200;
        max-height: 200;
    }
    #passphrase_label {
        font-family: 'Montserrat';
        font-weight: 500;
        font-size: 13px;
    }
    #passphrase_form QLineEdit {
        border-radius: 0px;
        min-height: 30px;
        margin: 0px 0px 10px 0px;
    }
    '''

    def __init__(self, controller, file_uuid, file_name):
        super().__init__()

        self.controller = controller
        self.file_uuid = file_uuid
        self.file_name = file_name

        self.setObjectName('export_dialog')
        self.setStyleSheet(self.CSS)
        self.setWindowFlags(Qt.Popup)
        self.setWindowModality(Qt.WindowModal)

        layout = QVBoxLayout(self)
        self.setLayout(layout)

        # Starting export message
        self.starting_export_message = SecureQLabel(_(
            'Preparing to export:\n' + self.file_name))
        self.starting_export_message.setWordWrap(True)

        # Widget to show error messages that occur during an export
        self.generic_error = QWidget()
        self.generic_error.setObjectName('gener_error')
        generic_error_layout = QHBoxLayout()
        self.generic_error.setLayout(generic_error_layout)
        self.error_status_code = SecureQLabel()
        generic_error_message = SecureQLabel(_('See your administrator for help.'))
        generic_error_message.setWordWrap(True)
        generic_error_layout.addWidget(self.error_status_code)
        generic_error_layout.addWidget(generic_error_message)

        # Insert USB Device Form
        self.insert_usb_form = QWidget()
        self.insert_usb_form.setObjectName('insert_usb_form')
        usb_form_layout = QVBoxLayout()
        self.insert_usb_form.setLayout(usb_form_layout)
        self.usb_error_message = SecureQLabel(_(
            'Either the drive is not LUKS-encrypted, or there is something '
            'else wrong with it.'))
        self.usb_error_message.setWordWrap(True)
        usb_instructions = SecureQLabel(_(
            'Please insert one of the export drives provisioned specifically '
            'for the SecureDrop Workstation.'))
        usb_instructions.setWordWrap(True)
        buttons = QWidget()
        buttons_layout = QHBoxLayout()
        buttons.setLayout(buttons_layout)
        usb_cancel_button = QPushButton(_('CANCEL'))
        retry_export_button = QPushButton(_('OK'))
        buttons_layout.addWidget(usb_cancel_button)
        buttons_layout.addWidget(retry_export_button)
        usb_form_layout.addWidget(self.usb_error_message)
        usb_form_layout.addWidget(usb_instructions)
        usb_form_layout.addWidget(buttons, alignment=Qt.AlignRight)

        # Passphrase Form
        self.passphrase_form = QWidget()
        self.passphrase_form.setObjectName('passphrase_form')
        passphrase_form_layout = QVBoxLayout()
        self.passphrase_form.setLayout(passphrase_form_layout)
        self.passphrase_error_message = SecureQLabel(_(
            'The passphrase provided did not work. Please try again.'))
        self.passphrase_error_message.setWordWrap(True)
        self.passphrase_instructions = SecureQLabel(_('Enter the passphrase for this drive'))
        self.passphrase_instructions.setWordWrap(True)
        passphrase_label = SecureQLabel(_('Passphrase'))
        passphrase_label.setObjectName('passphrase_label')
        self.passphrase_field = QLineEdit()
        self.passphrase_field.setEchoMode(QLineEdit.Password)
        buttons = QWidget()
        buttons_layout = QHBoxLayout()
        buttons.setLayout(buttons_layout)
        passphrase_cancel_button = QPushButton(_('CANCEL'))
        unlock_disk_button = QPushButton(_('SUBMIT'))
        buttons_layout.addWidget(passphrase_cancel_button)
        buttons_layout.addWidget(unlock_disk_button)
        passphrase_form_layout.addWidget(self.passphrase_error_message)
        passphrase_form_layout.addWidget(self.passphrase_instructions)
        passphrase_form_layout.addWidget(passphrase_label)
        passphrase_form_layout.addWidget(self.passphrase_field)
        passphrase_form_layout.addWidget(buttons, alignment=Qt.AlignRight)
        self.passphrase_error_message.hide()

        # Starting export message
        self.exporting_message = SecureQLabel(_(
            'File export in progress:\n' + self.file_name))
        self.exporting_message.setWordWrap(True)

        layout.addWidget(self.starting_export_message)
        layout.addWidget(self.exporting_message)
        layout.addWidget(self.generic_error)
        layout.addWidget(self.insert_usb_form)
        layout.addWidget(self.passphrase_form)

        self.starting_export_message.show()
        self.exporting_message.hide()
        self.generic_error.hide()
        self.insert_usb_form.hide()
        self.passphrase_form.hide()

        usb_cancel_button.clicked.connect(self.close)
        passphrase_cancel_button.clicked.connect(self.close)
        retry_export_button.clicked.connect(self._on_retry_export_button_clicked)
        unlock_disk_button.clicked.connect(self._on_unlock_disk_clicked)

        self.controller.export.preflight_check_call_failure.connect(
            self._on_preflight_check_call_failure, type=Qt.QueuedConnection)
        self.controller.export.export_usb_call_failure.connect(
            self._on_export_usb_call_failure, type=Qt.QueuedConnection)
        self.controller.export.preflight_check_call_success.connect(
            self._request_passphrase, type=Qt.QueuedConnection)
        self.controller.export.export_usb_call_success.connect(
            self._on_export_success, type=Qt.QueuedConnection)

    def export(self):
        self.controller.run_export_preflight_checks()

    @pyqtSlot()
    def _on_retry_export_button_clicked(self):
        self.starting_export_message.hide()
        self.controller.run_export_preflight_checks()

    @pyqtSlot()
    def _on_unlock_disk_clicked(self):
        self.passphrase_form.hide()
        self.exporting_message.show()
        passphrase = self.passphrase_field.text()
        self.controller.export_file_to_usb_drive(self.file_uuid, passphrase)

    @pyqtSlot()
    def _on_export_success(self):
        self.close()

    def _request_to_insert_usb_device(self, encryption_not_supported: bool = False):
        self.starting_export_message.hide()
        self.passphrase_form.hide()
        self.insert_usb_form.show()

        if encryption_not_supported:
            self.usb_error_message.show()
        else:
            self.usb_error_message.hide()

    @pyqtSlot()
    def _request_passphrase(self, bad_passphrase: bool = False):
        logger.debug('requesting passphrase... ')
        self.starting_export_message.hide()
        self.exporting_message.hide()
        self.insert_usb_form.hide()
        self.passphrase_form.show()

        if bad_passphrase:
            self.passphrase_instructions.hide()
            self.passphrase_error_message.show()
        else:
            self.passphrase_error_message.hide()
            self.passphrase_instructions.show()

    def _update(self, status):
        logger.debug('updating status... ')
        if status == ExportStatus.USB_NOT_CONNECTED.value:
            self._request_to_insert_usb_device()
        elif status == ExportStatus.BAD_PASSPHRASE.value:
            self._request_passphrase(True)
        elif status == ExportStatus.DISK_ENCRYPTION_NOT_SUPPORTED_ERROR.value:
            self._request_to_insert_usb_device(True)
        else:
            self.error_status_code.setText(_(status))
            self.generic_error.show()
            self.starting_export_message.hide()
            self.passphrase_form.hide()
            self.insert_usb_form.hide()

    @pyqtSlot(object)
    def _on_preflight_check_call_failure(self, error: ExportError):
        self._update(error.status)

    @pyqtSlot(object)
    def _on_export_usb_call_failure(self, error: ExportError):
        self._update(error.status)


class ConversationView(QWidget):
    """
    Renders a conversation.
    """

    CSS = '''
    #container {
        background: #f3f5f9;
    }
    #scroll {
        border: 0;
        background: #f3f5f9;
    }
    '''

    conversation_updated = pyqtSignal()

    MARGIN_LEFT = 38
    MARGIN_RIGHT = 20

    def __init__(self, source_db_object: Source, controller: Controller):
        super().__init__()

        self.source = source_db_object
        self.controller = controller

        # To hold currently displayed messages.
        self.current_messages = {}  # type: Dict[str, QWidget]

        # Set styles
        self.setStyleSheet(self.CSS)

        # Set layout
        main_layout = QVBoxLayout()
        self.setLayout(main_layout)

        # Set margins and spacing
        main_layout.setContentsMargins(0, 0, 0, 0)
        main_layout.setSpacing(0)

        self.container = QWidget()
        self.container.setObjectName('container')
        self.conversation_layout = QVBoxLayout()
        self.container.setLayout(self.conversation_layout)
        self.conversation_layout.setContentsMargins(self.MARGIN_LEFT, 0, self.MARGIN_RIGHT, 0)
        self.conversation_layout.setSpacing(0)
        self.container.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        self.scroll = QScrollArea()
        self.scroll.setObjectName('scroll')
        self.scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.scroll.setWidget(self.container)
        self.scroll.setWidgetResizable(True)

        # Flag to show if the current user has sent a reply. See issue #61.
        self.reply_flag = False

        # Completely unintuitive way to ensure the view remains scrolled to the bottom.
        sb = self.scroll.verticalScrollBar()
        sb.rangeChanged.connect(self.update_conversation_position)

        main_layout.addWidget(self.scroll)

        self.update_conversation(self.source.collection)

    def clear_conversation(self):
        while self.conversation_layout.count():
            child = self.conversation_layout.takeAt(0)
            if child.widget():
                child.widget().deleteLater()

    def update_conversation(self, collection: list) -> None:
        """
        Given a list of conversation items that reflect the new state of the
        conversation, this method does two things:

        * Checks if the conversation item already exists in the conversation.
          If so, it checks that it's still in the same position. If it isn't,
          the item is removed from its current position and re-added at the
          new position. Then the index meta-data on the widget is updated to
          reflect this change.
        * If the item is a new item, this is created (as before) and inserted
          into the conversation at the correct index.

        Things to note, speech bubbles and files have an index attribute which
        defines where they currently are. This is the attribute that's checked
        when the new conversation state (i.e. the collection argument) is
        passed into this method in case of a mismatch between where the widget
        has been and now is in terms of its index in the conversation.
        """
        self.controller.session.refresh(self.source)

        # Keep a temporary copy of the current conversation so we can delete any
        # items corresponding to deleted items in the source collection.
        current_conversation = self.current_messages.copy()

        for index, conversation_item in enumerate(collection):
            item_widget = current_conversation.get(conversation_item.uuid)
            if item_widget:
                current_conversation.pop(conversation_item.uuid)
                if item_widget.index != index:
                    # The existing widget is out of order.
                    # Remove / re-add it and update index details.
                    self.conversation_layout.removeWidget(item_widget)
                    item_widget.index = index
                    if isinstance(item_widget, ReplyWidget):
                        self.conversation_layout.insertWidget(index, item_widget,
                                                              alignment=Qt.AlignRight)
                    else:
                        self.conversation_layout.insertWidget(index, item_widget,
                                                              alignment=Qt.AlignLeft)
                # Check if text in item has changed, then update the
                # widget to reflect this change.
                if not isinstance(item_widget, FileWidget):
                    if (item_widget.message.text() != conversation_item.content) and \
                            conversation_item.content:
                        item_widget.message.setText(conversation_item.content)
            else:
                # add a new item to be displayed.
                if isinstance(conversation_item, Message):
                    self.add_message(conversation_item, index)
                elif isinstance(conversation_item, (DraftReply, Reply)):
                    self.add_reply(conversation_item, index)
                else:
                    self.add_file(conversation_item, index)

        # If any items remain in current_conversation, they are no longer in the
        # source collection and should be removed.
        for item_widget in current_conversation.values():
            self.conversation_layout.removeWidget(item_widget)

    def add_file(self, file: File, index):
        """
        Add a file from the source.
        """
        conversation_item = FileWidget(
            file.uuid,
            self.controller,
            self.controller.file_ready,
            self.controller.file_missing,
            index)
        self.conversation_layout.insertWidget(index, conversation_item, alignment=Qt.AlignLeft)
        self.current_messages[file.uuid] = conversation_item
        self.conversation_updated.emit()

    def update_conversation_position(self, min_val, max_val):
        """
        Handler called when a new item is added to the conversation. Ensures
        it's scrolled to the bottom and thus visible.
        """
        if self.reply_flag and max_val > 0:
            self.scroll.verticalScrollBar().setValue(max_val)
            self.reply_flag = False

    def add_message(self, message: Message, index) -> None:
        """
        Add a message from the source.
        """
        conversation_item = MessageWidget(
            message.uuid, str(message), self.controller.message_ready, index)
        self.conversation_layout.insertWidget(index, conversation_item, alignment=Qt.AlignLeft)
        self.current_messages[message.uuid] = conversation_item
        self.conversation_updated.emit()

    def add_reply(self, reply: Union[DraftReply, Reply], index) -> None:
        """
        Add a reply from a journalist to the source.
        """
        try:
            send_status = reply.send_status.name
        except AttributeError:
            send_status = 'SUCCEEDED'

        logger.debug('adding reply: with status {}'.format(send_status))
        conversation_item = ReplyWidget(
            reply.uuid,
            str(reply),
            send_status,
            self.controller.reply_ready,
            self.controller.reply_succeeded,
            self.controller.reply_failed,
            index)
        self.conversation_layout.insertWidget(index, conversation_item, alignment=Qt.AlignRight)
        self.current_messages[reply.uuid] = conversation_item

    def add_reply_from_reply_box(self, uuid: str, content: str) -> None:
        """
        Add a reply from the reply box.
        """
        index = len(self.current_messages)
        conversation_item = ReplyWidget(
            uuid,
            content,
            'PENDING',
            self.controller.reply_ready,
            self.controller.reply_succeeded,
            self.controller.reply_failed,
            index)
        self.conversation_layout.insertWidget(index, conversation_item, alignment=Qt.AlignRight)
        self.current_messages[uuid] = conversation_item

    def on_reply_sent(self, source_uuid: str, reply_uuid: str, reply_text: str) -> None:
        """
        Add the reply text sent from ReplyBoxWidget to the conversation.
        """
        self.reply_flag = True
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

        # Set layout
        layout = QVBoxLayout()
        self.setLayout(layout)

        # Set margins and spacing
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Create widgets
        self.conversation_title_bar = SourceProfileShortWidget(source, controller)
        self.conversation_view = ConversationView(source, controller)
        self.reply_box = ReplyBoxWidget(source, controller)

        # Add widgets
        layout.addWidget(self.conversation_title_bar)
        layout.addWidget(self.conversation_view)
        layout.addWidget(self.reply_box)

        # Connect reply_box to conversation_view
        self.reply_box.reply_sent.connect(self.conversation_view.on_reply_sent)
        self.conversation_view.conversation_updated.connect(
            self.conversation_title_bar.update_timestamp)


class ReplyBoxWidget(QWidget):
    """
    A textbox where a journalist can enter a reply.
    """

    CSS = '''
    #replybox_holder {
        min-height: 173px;
        max-height: 173px;
    }
    #replybox {
        background-color: #ffffff;
    }
    #replybox::disabled {
        background-color: #efefef;
    }
    QPushButton {
        border: none;
    }
    QPushButton:hover {
        background: #D3D8EA;
        border-radius: 8px;
    }
    QWidget#horizontal_line {
        min-height: 2px;
        max-height: 2px;
        background-color: rgba(42, 49, 157, 0.15);
        border: none;
    }
    '''

    reply_sent = pyqtSignal(str, str, str)

    def __init__(self, source: Source, controller: Controller) -> None:
        super().__init__()

        self.source = source
        self.controller = controller

        # Set css id
        self.setObjectName('replybox_holder')

        # Set styles
        self.setStyleSheet(self.CSS)

        # Set layout
        main_layout = QVBoxLayout()
        self.setLayout(main_layout)

        # Set margins
        main_layout.setContentsMargins(0, 0, 0, 0)
        main_layout.setSpacing(0)

        # Create top horizontal line
        horizontal_line = QWidget()
        horizontal_line.setObjectName('horizontal_line')

        # Create replybox
        self.replybox = QWidget()
        self.replybox.setObjectName('replybox')
        replybox_layout = QHBoxLayout(self.replybox)
        replybox_layout.setContentsMargins(32.6, 19, 27.3, 18)
        replybox_layout.setSpacing(0)

        # Create reply text box
        self.text_edit = ReplyTextEdit(self.source, self.controller)
        self.text_edit.setVerticalScrollBarPolicy(Qt.ScrollBarAlwaysOff)

        # Create reply send button (airplane)
        self.send_button = QPushButton()
        self.send_button.clicked.connect(self.send_reply)
        button_pixmap = load_image('send.svg')
        button_icon = QIcon(button_pixmap)
        self.send_button.setIcon(button_icon)
        self.send_button.setIconSize(QSize(56.5, 47))
        self.send_button.setShortcut(QKeySequence("Ctrl+Return"))
        self.send_button.setDefault(True)

        # Ensure TAB order from text edit -> send button
        self.setTabOrder(self.text_edit, self.send_button)

        # Set cursor.
        self.send_button.setCursor(QCursor(Qt.PointingHandCursor))

        # Add widgets to replybox
        replybox_layout.addWidget(self.text_edit)
        replybox_layout.addWidget(self.send_button, alignment=Qt.AlignBottom)

        # Add widgets
        main_layout.addWidget(horizontal_line)
        main_layout.addWidget(self.replybox)

        # Determine whether or not this widget should be enabled
        if self.controller.is_authenticated:
            self.enable()
        else:
            self.disable()

        # Text area refocus flag.
        self.refocus_after_sync = False

        # Connect signals to slots
        self.controller.authentication_state.connect(self._on_authentication_changed)
        self.controller.sync_events.connect(self._on_synced)

    def enable(self):
        self.text_edit.set_logged_in()
        self.replybox.setEnabled(True)
        self.send_button.show()

    def disable(self):
        self.text_edit.set_logged_out()
        self.replybox.setEnabled(False)
        self.send_button.hide()

    def send_reply(self) -> None:
        """
        Send reply and emit a signal so that the gui can be updated immediately indicating
        that it is a pending reply.
        """
        reply_text = self.text_edit.toPlainText().strip()
        if reply_text:
            self.text_edit.clearFocus()  # Fixes #691
            self.text_edit.setText('')
            reply_uuid = str(uuid4())
            self.controller.send_reply(self.source.uuid, reply_uuid, reply_text)
            self.reply_sent.emit(self.source.uuid, reply_uuid, reply_text)

    def _on_authentication_changed(self, authenticated: bool) -> None:
        if authenticated:
            self.enable()
        else:
            self.disable()

    def _on_synced(self, data: str) -> None:
        if data == 'syncing' and self.text_edit.hasFocus():
            self.refocus_after_sync = True
        elif data == 'synced' and self.refocus_after_sync:
            self.text_edit.setFocus()
        else:
            self.refocus_after_sync = False


class ReplyTextEdit(QPlainTextEdit):
    """
    A plaintext textbox with placeholder that disapears when clicked and
    a richtext lable on top to replace the placeholder functionality
    """

    CSS = '''
    #reply_textedit {
        font-family: 'Montserrat';
        font-weight: 400;
        font-size: 18px;
        border: none;
        margin-right: 30.2px;
    }
    #reply_placeholder {
        font-family: 'Montserrat';
        font-weight: 400;
        font-size: 18px;
        color: #404040;
    }
    #reply_placeholder::disabled {
        color: rgba(42, 49, 157, 0.6);
    }
    '''

    def __init__(self, source, controller):
        super().__init__()
        self.controller = controller
        self.source = source

        self.setObjectName('reply_textedit')
        self.setStyleSheet(self.CSS)

        self.setTabChangesFocus(True)  # Needed so we can TAB to send button.

        self.placeholder = QLabel()
        self.placeholder.setObjectName("reply_placeholder")
        self.placeholder.setParent(self)
        self.placeholder.move(QPoint(3, 4))  # make label match text below
        self.set_logged_in()
        # Set cursor.
        self.setCursor(QCursor(Qt.IBeamCursor))

    def focusInEvent(self, e):
        # override default behavior: when reply text box is focused, the placeholder
        # disappears instead of only doing so when text is typed
        if self.toPlainText() == "":
            self.placeholder.hide()
        super(ReplyTextEdit, self).focusInEvent(e)

    def focusOutEvent(self, e):
        if self.toPlainText() == "":
            self.placeholder.show()
        super(ReplyTextEdit, self).focusOutEvent(e)

    def set_logged_in(self):
        if self.source.public_key:
            self.setEnabled(True)
            source_name = "<strong><font color=\"#24276d\">{}</font></strong>".format(
                self.source.journalist_designation)
            placeholder = _("Compose a reply to ") + source_name
        else:
            self.setEnabled(False)
            msg = "<strong><font color=\"#24276d\">Awaiting action</font></strong>"
            placeholder = msg + " from the source to enable replies."
        self.placeholder.setText(placeholder)
        self.placeholder.adjustSize()

    def set_logged_out(self):
        text = "<strong><font color=\"#2a319d\">" + _("Sign in") + " </font></strong>" + \
            _("to compose or send a reply")
        self.placeholder.setText(text)
        self.placeholder.adjustSize()
        self.setEnabled(False)

    def setText(self, text):
        if text == "":
            self.placeholder.show()
        else:
            self.placeholder.hide()
        super(ReplyTextEdit, self).setPlainText(text)


class DeleteSourceAction(QAction):
    """Use this action to delete the source record."""

    def __init__(self, source, parent, controller):
        self.source = source
        self.controller = controller
        self.text = _("Delete source account")

        super().__init__(self.text, parent)

        self.messagebox = DeleteSourceMessageBox(self.source, self.controller)
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

        actions = (DeleteSourceAction(self.source, self, self.controller),)
        for action in actions:
            self.addAction(action)


class SourceMenuButton(QToolButton):
    """An ellipse based source menu button.

    This button is responsible for launching the source menu on click.
    """

    CSS = '''
    #ellipsis_button {
        border: none;
        margin: 5px 0px 0px 0px;
        padding-left: 8px;
    }
    QToolButton::menu-indicator {
        image: none;
    }
    '''

    def __init__(self, source, controller):
        super().__init__()
        self.controller = controller
        self.source = source

        self.setObjectName('ellipsis_button')
        self.setStyleSheet(self.CSS)

        self.setIcon(load_icon("ellipsis.svg"))
        self.setIconSize(QSize(22, 4))  # Set to the size of the svg viewBox

        self.menu = SourceMenu(self.source, self.controller)
        self.setMenu(self.menu)

        self.setPopupMode(QToolButton.InstantPopup)
        # Set cursor.
        self.setCursor(QCursor(Qt.PointingHandCursor))


class TitleLabel(QLabel):
    """The title for a conversation."""

    CSS = '''
    #conversation-title-source-name {
        font-family: 'Montserrat';
        font-weight: 400;
        font-size: 24px;
        color: #2a319d;
        padding-left: 4px;
    }
    '''

    def __init__(self, text):
        super().__init__(_(text))

        # Set css id
        self.setObjectName('conversation-title-source-name')

        # Set styles
        self.setStyleSheet(self.CSS)


class LastUpdatedLabel(QLabel):
    """Time the conversation was last updated."""

    CSS = '''
    #conversation-title-date {
        font-family: 'Montserrat';
        font-weight: 200;
        font-size: 24px;
        color: #2a319d;
    }
    '''

    def __init__(self, last_updated):
        super().__init__(last_updated)

        # Set css id
        self.setObjectName('conversation-title-date')

        # Set styles
        self.setStyleSheet(self.CSS)


class SourceProfileShortWidget(QWidget):
    """A widget for displaying short view for Source.

    It contains below information.
    1. Journalist designation
    2. A menu to perform various operations on Source.
    """

    CSS = '''
    QWidget#horizontal_line {
        min-height: 2px;
        max-height: 2px;
        background-color: rgba(42, 49, 157, 0.15);
        padding-left: 12px;
        padding-right: 12px;
    }
    '''

    MARGIN_LEFT = 25
    MARGIN_RIGHT = 17
    VERTICAL_MARGIN = 14

    def __init__(self, source, controller):
        super().__init__()

        self.source = source
        self.controller = controller

        # Set styles
        self.setStyleSheet(self.CSS)

        # Set layout
        layout = QVBoxLayout()
        self.setLayout(layout)

        # Create header
        header = QWidget()
        header_layout = QHBoxLayout(header)
        header_layout.setContentsMargins(
            self.MARGIN_LEFT, self.VERTICAL_MARGIN, self.MARGIN_RIGHT, self.VERTICAL_MARGIN)
        title = TitleLabel(self.source.journalist_designation)
        self.updated = LastUpdatedLabel(_(arrow.get(self.source.last_updated).format('DD MMM')))
        menu = SourceMenuButton(self.source, self.controller)
        header_layout.addWidget(title, alignment=Qt.AlignLeft)
        header_layout.addStretch()
        header_layout.addWidget(self.updated, alignment=Qt.AlignRight)
        header_layout.addWidget(menu, alignment=Qt.AlignRight)

        # Create horizontal line
        horizontal_line = QWidget()
        horizontal_line.setObjectName('horizontal_line')
        horizontal_line.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        # Add widgets
        layout.addWidget(header)
        layout.addWidget(horizontal_line)

    def update_timestamp(self):
        """
        Ensure the timestamp is always kept up to date with the latest activity
        from the source.
        """
        self.updated.setText(_(arrow.get(self.source.last_updated).format('DD MMM')))
