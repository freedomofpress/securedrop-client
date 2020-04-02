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
from typing import Dict, List, Union, Optional  # noqa: F401
from uuid import uuid4
from PyQt5.QtCore import Qt, pyqtSlot, pyqtSignal, QEvent, QTimer, QSize, pyqtBoundSignal, \
    QObject, QPoint
from PyQt5.QtGui import QIcon, QPalette, QBrush, QColor, QFont, QLinearGradient, QKeySequence, \
    QCursor, QKeyEvent, QPixmap
from PyQt5.QtWidgets import QApplication, QListWidget, QLabel, QWidget, QListWidgetItem, \
    QHBoxLayout, QVBoxLayout, QLineEdit, QScrollArea, QDialog, QAction, QMenu, QMessageBox, \
    QToolButton, QSizePolicy, QPlainTextEdit, QStatusBar, QGraphicsDropShadowEffect, QPushButton, \
    QDialogButtonBox
import sqlalchemy.orm.exc

from securedrop_client import __version__ as sd_version
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
        self.setPalette(self.online_palette)

    def set_logged_out(self):
        self.sync_icon.disable()
        self.setPalette(self.offline_palette)

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

    def setup(self, controller):
        self.controller = controller

    def update_message(self, message: str, duration: int) -> None:
        """
        Display a status message to the user for a given duration. If the duration is zero,
        continuously show message.
        """
        self.status_bar.showMessage(message, duration)
        new_width = self.fontMetrics().horizontalAdvance(message)
        self.status_bar.setMinimumWidth(new_width)
        self.status_bar.reformat()

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

        # User button
        self.user_button = UserButton()

        # User icon
        self.user_icon = UserIconLabel()
        self.user_icon.setObjectName('user_icon')  # Set css id
        self.user_icon.setFixedSize(QSize(30, 30))
        self.user_icon.setAlignment(Qt.AlignCenter)
        self.user_icon_font = QFont()
        self.user_icon_font.setLetterSpacing(QFont.AbsoluteSpacing, 0.58)
        self.user_icon.setFont(self.user_icon_font)
        self.user_icon.clicked.connect(self.user_button.click)
        # Set cursor.
        self.user_icon.setCursor(QCursor(Qt.PointingHandCursor))

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


class UserIconLabel(QLabel):
    """
    Makes a label clickable. (For the label containing the user icon.)
    """

    clicked = pyqtSignal()

    def mousePressEvent(self, e):
        self.clicked.emit()


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
        self.source_conversations = {}  # type: Dict[str, SourceConversationWrapper]

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
        if sources:
            self.empty_conversation_view.show_no_source_selected_message()
            self.empty_conversation_view.show()
        else:
            self.empty_conversation_view.show_no_sources_message()
            self.empty_conversation_view.show()

        if self.source_list.source_widgets:
            # The source list already contains sources.
            deleted_sources = self.source_list.update(sources)
            for source_uuid in deleted_sources:
                # Then call the function to remove the wrapper and its children.
                self.delete_conversation(source_uuid)
        else:
            # We have an empty source list, so do an initial update.
            self.source_list.initial_update(sources)

    def on_source_changed(self):
        """
        Show conversation for the currently-selected source if it hasn't been deleted. If the
        current source no longer exists, clear the conversation for that source.
        """
        source = self.source_list.get_selected_source()

        if not source:
            return

        self.controller.session.refresh(source)
        # Try to get the SourceConversationWrapper from the persistent dict,
        # else we create it.
        try:
            logger.debug('Drawing source conversation for {}'.format(source.uuid))
            conversation_wrapper = self.source_conversations[source.uuid]

            # Redraw the conversation view such that new messages, replies, files appear.
            conversation_wrapper.conversation_view.update_conversation(source.collection)
        except KeyError:
            conversation_wrapper = SourceConversationWrapper(source, self.controller)
            self.source_conversations[source.uuid] = conversation_wrapper

        self.set_conversation(conversation_wrapper)

    def delete_conversation(self, source_uuid: str) -> None:
        """
        When we delete a source, we should delete its SourceConversationWrapper,
        and remove the reference to it in self.source_conversations
        """
        try:
            logger.debug('Deleting SourceConversationWrapper for {}'.format(source_uuid))
            conversation_wrapper = self.source_conversations[source_uuid]
            conversation_wrapper.deleteLater()
            del self.source_conversations[source_uuid]
        except KeyError:
            logger.debug('No SourceConversationWrapper for {} to delete'.format(source_uuid))

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


class EmptyConversationView(QWidget):

    CSS = '''
    #bullet {
        margin: 4px 0px 0px 0px;
        font-size: 35px;
        font-weight: 600;
    }
    #no_sources {
        min-width: 520px;
        max-width: 600px;
        text-align: left;
    }
    #no_source_selected {
        min-width: 520px;
        max-width: 520px;
        text-align: left;
    }
    QLabel {
        font-family: Montserrat;
        font-weight: 400;
        font-size: 35px;
        color: #a5b3e9;
    }
    #instructions {
        font-weight: 500;
    }
    '''

    MARGIN = 30
    NEWLINE_HEIGHT_PX = 35

    def __init__(self):
        super().__init__()

        # Set id and styles
        self.setObjectName('view')
        self.setStyleSheet(self.CSS)

        # Set layout
        layout = QHBoxLayout()
        layout.setContentsMargins(self.MARGIN, self.MARGIN, self.MARGIN, self.MARGIN)
        self.setLayout(layout)

        # Create widgets
        self.no_sources = QWidget()
        self.no_sources.setObjectName('no_sources')
        no_sources_layout = QVBoxLayout()
        self.no_sources.setLayout(no_sources_layout)
        no_sources_instructions = QLabel(_('Nothing to see just yet!'))
        no_sources_instructions.setObjectName('instructions')
        no_sources_instructions.setWordWrap(True)
        no_sources_instruction_details1 = QLabel(
            _('Source submissions will be listed to the left, once downloaded and decrypted.'))
        no_sources_instruction_details1.setWordWrap(True)
        no_sources_instruction_details2 = QLabel(
            _('This is where you will read messages, reply to sources, and work with files.'))
        no_sources_instruction_details2.setWordWrap(True)
        no_sources_layout.addWidget(no_sources_instructions)
        no_sources_layout.addSpacing(self.NEWLINE_HEIGHT_PX)
        no_sources_layout.addWidget(no_sources_instruction_details1)
        no_sources_layout.addSpacing(self.NEWLINE_HEIGHT_PX)
        no_sources_layout.addWidget(no_sources_instruction_details2)

        self.no_source_selected = QWidget()
        self.no_sources.setObjectName('no_sources')
        no_source_selected_layout = QVBoxLayout()
        self.no_source_selected.setLayout(no_source_selected_layout)
        no_source_selected_instructions = QLabel(_('Select a source from the list, to:'))
        no_source_selected_instructions.setObjectName('instructions')
        no_source_selected_instructions.setWordWrap(True)
        bullet1 = QWidget()
        bullet1_layout = QHBoxLayout()
        bullet1_layout.setContentsMargins(0, 0, 0, 0)
        bullet1.setLayout(bullet1_layout)
        bullet1_bullet = QLabel('·')
        bullet1_bullet.setObjectName('bullet')
        bullet1_layout.addWidget(bullet1_bullet)
        bullet1_layout.addWidget(QLabel(_('Read a conversation')))
        bullet1_layout.addStretch()
        bullet2 = QWidget()
        bullet2_layout = QHBoxLayout()
        bullet2_layout.setContentsMargins(0, 0, 0, 0)
        bullet2.setLayout(bullet2_layout)
        bullet2_bullet = QLabel('·')
        bullet2_bullet.setObjectName('bullet')
        bullet2_layout.addWidget(bullet2_bullet)
        bullet2_layout.addWidget(QLabel(_('View or retrieve files')))
        bullet2_layout.addStretch()
        bullet3 = QWidget()
        bullet3_layout = QHBoxLayout()
        bullet3_layout.setContentsMargins(0, 0, 0, 0)
        bullet3.setLayout(bullet3_layout)
        bullet3_bullet = QLabel('·')
        bullet3_bullet.setObjectName('bullet')
        bullet3_layout.addWidget(bullet3_bullet)
        bullet3_layout.addWidget(QLabel(_('Send a response')))
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

    def show_no_sources_message(self):
        self.no_sources.show()
        self.no_source_selected.hide()

    def show_no_source_selected_message(self):
        self.no_sources.hide()
        self.no_source_selected.show()


class SourceListWidgetItem(QListWidgetItem):

    def __lt__(self, other):
        """
        Used for ordering widgets by timestamp of last interaction.
        """
        lw = self.listWidget()
        me = lw.itemWidget(self)
        them = lw.itemWidget(other)
        if me and them:
            my_ts = arrow.get(me.source.last_updated)
            other_ts = arrow.get(them.source.last_updated)
            return my_ts < other_ts
        return True


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
        self.setFixedWidth(540)
        self.setUniformItemSizes(True)

        # Set layout.
        layout = QVBoxLayout(self)
        self.setLayout(layout)

        # Enable ordering.
        self.setSortingEnabled(True)

        # To hold references to SourceWidget instances indexed by source UUID.
        self.source_widgets = {}

    def setup(self, controller):
        self.controller = controller
        self.controller.reply_succeeded.connect(self.set_snippet)
        self.controller.message_ready.connect(self.set_snippet)
        self.controller.reply_ready.connect(self.set_snippet)
        self.controller.file_ready.connect(self.set_snippet)
        self.controller.file_missing.connect(self.set_snippet)

    def update(self, sources: List[Source]) -> List[str]:
        """
        Update the list with the passed in list of sources.
        """
        # Delete widgets that no longer exist in source list
        source_uuids = [source.uuid for source in sources]
        deleted_uuids = []
        for i in range(self.count()):
            list_item = self.item(i)
            list_widget = self.itemWidget(list_item)

            if list_widget and list_widget.source_uuid not in source_uuids:
                if list_item.isSelected():
                    self.setCurrentItem(None)

                try:
                    del self.source_widgets[list_widget.source_uuid]
                except KeyError:
                    pass

                self.takeItem(i)
                deleted_uuids.append(list_widget.source_uuid)
                list_widget.deleteLater()

        # Create new widgets for new sources
        widget_uuids = [self.itemWidget(self.item(i)).source_uuid for i in range(self.count())]
        for source in sources:
            if source.uuid in widget_uuids:
                try:
                    self.source_widgets[source.uuid].update()
                except sqlalchemy.exc.InvalidRequestError as e:
                    logger.error(
                        "Could not update SourceWidget for source %s; deleting it. Error was: %s",
                        source.uuid,
                        e
                    )
                    deleted_uuids.append(source.uuid)
                    self.source_widgets[source.uuid].deleteLater()
                    del self.source_widgets[list_widget.source_uuid]
            else:
                new_source = SourceWidget(self.controller, source)
                self.source_widgets[source.uuid] = new_source

                list_item = SourceListWidgetItem()
                self.insertItem(0, list_item)
                list_item.setSizeHint(new_source.sizeHint())
                self.setItemWidget(list_item, new_source)

        # Sort..!
        self.sortItems(Qt.DescendingOrder)
        return deleted_uuids

    def initial_update(self, sources: List[Source]):
        """
        Initialise the list with the passed in list of sources.
        """
        self.add_source(sources)

    def add_source(self, sources, slice_size=1):
        """
        Add a slice of sources, and if necessary, reschedule the addition of
        more sources.
        """

        def schedule_source_management(slice_size=slice_size):
            if not sources:
                # Nothing more to do.
                return
            # Process the remaining "slice_size" number of sources.
            sources_slice = sources[:slice_size]
            for source in sources_slice:
                new_source = SourceWidget(self.controller, source)
                self.source_widgets[source.uuid] = new_source
                list_item = SourceListWidgetItem(self)
                list_item.setSizeHint(new_source.sizeHint())

                self.insertItem(0, list_item)
                self.setItemWidget(list_item, new_source)
            # ATTENTION! 32 is an arbitrary number arrived at via
            # experimentation. It adds plenty of sources, but doesn't block
            # for a noticable amount of time.
            new_slice_size = min(32, slice_size * 2)
            # Call add_source again for the remaining sources.
            self.add_source(sources[slice_size:], new_slice_size)

        # Schedule the closure defined above in the next iteration of the
        # Qt event loop (thus unblocking the UI).
        QTimer.singleShot(1, schedule_source_management)

    def get_selected_source(self):
        if not self.selectedItems():
            return None

        source_item = self.selectedItems()[0]
        source_widget = self.itemWidget(source_item)
        if source_widget and source_exists(self.controller.session, source_widget.source_uuid):
            return source_widget.source

    def get_source_widget(self, source_uuid: str) -> Optional[QListWidget]:
        '''
        First try to get the source widget from the cache, then look for it in the SourceList.
        '''
        try:
            source_widget = self.source_widgets[source_uuid]
            return source_widget
        except KeyError:
            pass

        for i in range(self.count()):
            list_item = self.item(i)
            source_widget = self.itemWidget(list_item)
            if source_widget and source_widget.source_uuid == source_uuid:
                return source_widget

        return None

    @pyqtSlot(str, str, str)
    def set_snippet(self, source_uuid: str, collection_item_uuid: str, content: str) -> None:
        '''
        Set the source widget's preview snippet with the supplied content.

        Note: The signal's `collection_item_uuid` is not needed for setting the preview snippet. It
        is used by other signal handlers.
        '''
        source_widget = self.get_source_widget(source_uuid)
        if source_widget:
            source_widget.set_snippet(source_uuid, content)


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
    #source_deleted {
        font-family: 'Source Sans Pro';
        font-weight: 400;
        font-size: 13px;
        color: #ff3366;
    }
    QLabel#source_name {
        font-family: 'Montserrat';
        font-weight: 500;
        font-size: 13px;
        color: #383838;
        padding-top: 2px;
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
    PREVIEW_WIDTH = 412
    PREVIEW_HEIGHT = 60

    def __init__(self, controller: Controller, source: Source):
        super().__init__()

        self.controller = controller
        self.controller.source_deleted.connect(self._on_source_deleted)
        self.controller.source_deletion_failed.connect(self._on_source_deletion_failed)

        # Store source
        self.source_uuid = source.uuid
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

        retain_space = self.sizePolicy()
        retain_space.setRetainSizeWhenHidden(True)

        # Set up gutter
        self.gutter = QWidget()
        self.gutter.setObjectName('gutter')
        self.gutter.setSizePolicy(retain_space)
        gutter_layout = QVBoxLayout(self.gutter)
        gutter_layout.setContentsMargins(0, 0, 0, 0)
        gutter_layout.setSpacing(0)
        self.star = StarToggleButton(self.controller, self.source_uuid, source.is_starred)
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
        self.preview = SecureQLabel(max_length=self.PREVIEW_WIDTH)
        self.preview.setObjectName('preview')
        self.preview.setFixedSize(QSize(self.PREVIEW_WIDTH, self.PREVIEW_HEIGHT))
        self.waiting_delete_confirmation = QLabel('Deletion in progress')
        self.waiting_delete_confirmation.setObjectName('source_deleted')
        self.waiting_delete_confirmation.setFixedSize(
            QSize(self.PREVIEW_WIDTH, self.PREVIEW_HEIGHT))
        self.waiting_delete_confirmation.hide()
        summary_layout.addWidget(self.name)
        summary_layout.addWidget(self.preview)
        summary_layout.addWidget(self.waiting_delete_confirmation)

        # Set up metadata
        self.metadata = QWidget()
        self.metadata.setObjectName('metadata')
        self.metadata.setSizePolicy(retain_space)
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

    def update(self):
        """
        Updates the displayed values with the current values from self.source.
        """
        try:
            self.controller.session.refresh(self.source)
            self.timestamp.setText(_(arrow.get(self.source.last_updated).format('DD MMM')))
            self.name.setText(self.source.journalist_designation)

            if not self.source.server_collection:
                self.set_snippet(self.source_uuid, '')
            else:
                last_collection_obj = self.source.server_collection[-1]
                self.set_snippet(self.source_uuid, str(last_collection_obj))

            if self.source.document_count == 0:
                self.paperclip.hide()
            self.star.update(self.source.is_starred)
        except sqlalchemy.exc.InvalidRequestError as e:
            logger.error(f"Could not update SourceWidget for source {self.source_uuid}: {e}")
            raise

    def set_snippet(self, source_uuid: str, content: str):
        """
        Update the preview snippet if the source_uuid matches our own.
        """
        if source_uuid != self.source_uuid:
            return

        self.preview.setText(content)

    def delete_source(self, event):
        if self.controller.api is None:
            self.controller.on_action_requiring_login()
            return
        else:
            messagebox = DeleteSourceMessageBox(self.source, self.controller)
            messagebox.launch()

    @pyqtSlot(str)
    def _on_source_deleted(self, source_uuid: str):
        if self.source_uuid == source_uuid:
            self.gutter.hide()
            self.metadata.hide()
            self.preview.hide()
            self.waiting_delete_confirmation.show()

    @pyqtSlot(str)
    def _on_source_deletion_failed(self, source_uuid: str):
        if self.source_uuid == source_uuid:
            self.waiting_delete_confirmation.hide()
            self.gutter.show()
            self.metadata.show()
            self.preview.show()


class StarToggleButton(SvgToggleButton):
    """
    A button that shows whether or not a source is starred
    """

    css = '''
    #star_button {
        border: none;
    }
    '''

    def __init__(self, controller: Controller, source_uuid: str, is_starred: bool):
        super().__init__(on='star_on.svg', off='star_off.svg', svg_size=QSize(16, 16))

        self.controller = controller
        self.source_uuid = source_uuid
        self.is_starred = is_starred
        self.pending_count = 0
        self.wait_until_next_sync = False

        self.controller.authentication_state.connect(self.on_authentication_changed)
        self.controller.star_update_failed.connect(self.on_star_update_failed)
        self.controller.star_update_successful.connect(self.on_star_update_successful)
        self.installEventFilter(self)

        self.setObjectName('star_button')
        self.setStyleSheet(self.css)
        self.setFixedSize(QSize(20, 20))

        self.pressed.connect(self.on_pressed)
        self.setCheckable(True)
        self.setChecked(self.is_starred)

        if not self.controller.is_authenticated:
            self.disable_toggle()

    def disable_toggle(self):
        """
        Unset `checkable` so that the star cannot be toggled.

        Disconnect the `pressed` signal from previous handler and connect it to the offline handler.
        """
        self.pressed.disconnect()
        self.pressed.connect(self.on_pressed_offline)

        # If the source is starred, we must update the icon so that the off state continues to show
        # the source as starred. We could instead disable the button, which will continue to show
        # the star as checked, but Qt will also gray out the star, which we don't want.
        if self.is_starred:
            self.set_icon(on='star_on.svg', off='star_on.svg')
        self.setCheckable(False)

    def enable_toggle(self):
        """
        Enable the widget.

        Disconnect the pressed signal from previous handler, set checkable so that the star can be
        toggled, and connect to the online toggle handler.

        Note: We must update the icon in case it was modified after being disabled.
        """
        self.pressed.disconnect()
        self.pressed.connect(self.on_pressed)
        self.setCheckable(True)
        self.set_icon(on='star_on.svg', off='star_off.svg')  # Undo icon change from disable_toggle

    def eventFilter(self, obj, event):
        """
        If the button is checkable then we show a hover state.
        """
        if not self.isCheckable():
            return QObject.event(obj, event)

        t = event.type()
        if t == QEvent.HoverEnter:
            self.setIcon(load_icon('star_hover.svg'))
        elif t == QEvent.HoverLeave or t == QEvent.MouseButtonPress:
            self.set_icon(on='star_on.svg', off='star_off.svg')

        return QObject.event(obj, event)

    @pyqtSlot(bool)
    def on_authentication_changed(self, authenticated: bool) -> None:
        """
        Set up handlers based on whether or not the user is authenticated. Connect to 'pressed'
        event instead of 'toggled' event when not authenticated because toggling will be disabled.
        """
        if authenticated:
            self.pending_count = 0
            self.enable_toggle()
            self.setChecked(self.is_starred)
        else:
            self.disable_toggle()

    @pyqtSlot()
    def on_pressed(self) -> None:
        """
        Tell the controller to make an API call to update the source's starred field.
        """
        self.controller.update_star(self.source_uuid, self.isChecked())
        self.is_starred = not self.is_starred
        self.pending_count = self.pending_count + 1
        self.wait_until_next_sync = True

    @pyqtSlot()
    def on_pressed_offline(self) -> None:
        """
        Show error message when not authenticated.
        """
        self.controller.on_action_requiring_login()

    @pyqtSlot(bool)
    def update(self, is_starred: bool) -> None:
        """
        If star was updated via the Journalist Interface or by another instance of the client, then
        self.is_starred will not match the server and will need to be updated.
        """
        if not self.controller.is_authenticated:
            return

        # Wait until ongoing star jobs are finished before checking if it matches with the server
        if self.pending_count > 0:
            return

        # Wait until next sync to avoid the possibility of updating the star with outdated source
        # information in case the server just received the star request.
        if self.wait_until_next_sync:
            self.wait_until_next_sync = False
            return

        if self.is_starred != is_starred:
            self.is_starred = is_starred
            self.setChecked(self.is_starred)

    @pyqtSlot(str, bool)
    def on_star_update_failed(self, source_uuid: str, is_starred: bool) -> None:
        """
        If the star update failed to update on the server, toggle back to previous state.
        """
        if self.source_uuid == source_uuid:
            self.is_starred = is_starred
            self.pending_count = self.pending_count - 1
            QTimer.singleShot(250, lambda: self.setChecked(self.is_starred))

    @pyqtSlot(str)
    def on_star_update_successful(self, source_uuid: str) -> None:
        """
        If the star update succeeded, set pending to False so the sync can update the star field
        """
        if self.source_uuid == source_uuid:
            self.pending_count = self.pending_count - 1


class DeleteSourceMessageBox:
    """Use this to display operation details and confirm user choice."""

    def __init__(self, source, controller):
        self.source = source
        self.source_uuid = source.uuid
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
            logger.debug(f'Deleting source {self.source_uuid}')
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
        self.error_status_bar = SecureQLabel(wordwrap=False)
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
        padding-left: 5px;
    }
    '''

    MIN_PASSWORD_LEN = 14  # Journalist.MIN_PASSWORD_LEN on server
    MAX_PASSWORD_LEN = 128  # Journalist.MAX_PASSWORD_LEN on server
    MIN_JOURNALIST_USERNAME = 3  # Journalist.MIN_USERNAME_LEN on server

    def __init__(self, parent):
        self.parent = parent
        super().__init__(self.parent)

        # Set modal
        self.setModal(True)

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
        application_version_label = QLabel(_("SecureDrop Client v") + sd_version)
        application_version_label.setAlignment(Qt.AlignHCenter)
        application_version_label.setStyleSheet("QLabel {color: #9fddff;}")
        application_version_layout.addWidget(application_version_label)

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
        self.submit.setText(_("SIGN IN"))
        self.error_bar.set_message(message)

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
                self.error(_('That username won\'t work.\n'
                             'It should be at least 3 characters long.'))
                return

            # Validate password
            if len(password) < self.MIN_PASSWORD_LEN or len(password) > self.MAX_PASSWORD_LEN:
                self.setDisabled(False)
                self.error(_('That passphrase won\'t work.\n'
                             'It should be between 14 and 128 characters long.'))
                return

            # Validate 2FA token
            try:
                int(tfa_token)
            except ValueError:
                self.setDisabled(False)
                self.error(_('That two-factor code won\'t work.\n'
                             'It should only contain numerals.'))
                return
            self.submit.setText(_("SIGNING IN"))
            self.controller.login(username, password, tfa_token)
        else:
            self.setDisabled(False)
            self.error(_('Please enter a username, passphrase and '
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
    }
    #message {
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
    }
    '''

    TOP_MARGIN = 28
    BOTTOM_MARGIN = 10

    def __init__(self, message_uuid: str, text: str, update_signal, index: int) -> None:
        super().__init__()
        self.uuid = message_uuid
        self.index = index

        # Set styles
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

        # Color bar
        self.color_bar = QWidget()
        self.color_bar.setObjectName('color_bar')

        # Speech bubble
        speech_bubble = QWidget()
        speech_bubble.setObjectName('speech_bubble')
        speech_bubble_layout = QVBoxLayout()
        speech_bubble.setLayout(speech_bubble_layout)
        speech_bubble_layout.addWidget(self.message)
        speech_bubble_layout.addWidget(self.color_bar)
        speech_bubble_layout.setContentsMargins(0, 0, 0, 0)
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
    def _update_text(self, source_id: str, message_uuid: str, text: str) -> None:
        """
        Conditionally update this SpeechBubble's text if and only if the message_uuid of the emitted
        signal matches the uuid of this speech bubble.
        """
        if message_uuid == self.uuid:
            self.message.setText(text)


class MessageWidget(SpeechBubble):
    """
    Represents an incoming message from the source.
    """

    def __init__(self, message_uuid: str, message: str, update_signal, index: int) -> None:
        super().__init__(message_uuid, message, update_signal, index)


class ReplyWidget(SpeechBubble):
    """
    Represents a reply to a source.
    """

    CSS_MESSAGE_REPLY_FAILED = '''
        font-family: 'Source Sans Pro';
        font-weight: 400;
        font-size: 15px;
        background-color: #fff;
        color: #3b3b3b;
        padding: 16px;
    '''

    CSS_COLOR_BAR_REPLY_FAILED = '''
        min-height: 5px;
        max-height: 5px;
        background-color: #ff3366;
        border: 0px;
    '''

    CSS_ERROR_MESSAGE_REPLY_FAILED = '''
        font-family: 'Source Sans Pro';
        font-weight: 500;
        font-size: 13px;
        color: #ff3366;
    '''

    CSS_MESSAGE_REPLY_SUCCEEDED = '''
        font-family: 'Source Sans Pro';
        font-weight: 400;
        font-size: 15px;
        background-color: #fff;
        color: #3b3b3b;
        padding: 16px;
    '''

    CSS_COLOR_BAR_REPLY_SUCCEEDED = '''
        min-height: 5px;
        max-height: 5px;
        background-color: #0065db;
        border: 0px;
    '''

    CSS_MESSAGE_REPLY_PENDING = '''
        font-family: 'Source Sans Pro';
        font-weight: 400;
        font-size: 15px;
        color: #A9AAAD;
        background-color: #F7F8FC;
        padding: 16px;
    '''

    CSS_COLOR_BAR_REPLY_PENDING = '''
        min-height: 5px;
        max-height: 5px;
        background-color: #0065db;
        border: 0px;
    '''

    def __init__(
        self,
        message_uuid: str,
        message: str,
        reply_status: str,
        update_signal,
        message_succeeded_signal,
        message_failed_signal,
        index: int,
    ) -> None:
        super().__init__(message_uuid, message, update_signal, index)
        self.uuid = message_uuid

        error_icon = SvgLabel('error_icon.svg', svg_size=QSize(12, 12))
        error_icon.setObjectName('error_icon')  # Set css id
        error_icon.setFixedWidth(12)
        error_message = SecureQLabel('Failed to send', wordwrap=False)
        error_message.setObjectName('error_message')
        error_message.setStyleSheet(self.CSS_ERROR_MESSAGE_REPLY_FAILED)

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
            self.message.setStyleSheet(self.CSS_MESSAGE_REPLY_SUCCEEDED)
            self.color_bar.setStyleSheet(self.CSS_COLOR_BAR_REPLY_SUCCEEDED)
            self.error.hide()
        elif status == 'FAILED':
            self.message.setStyleSheet(self.CSS_MESSAGE_REPLY_FAILED)
            self.color_bar.setStyleSheet(self.CSS_COLOR_BAR_REPLY_FAILED)
            self.error.show()
        elif status == 'PENDING':
            self.message.setStyleSheet(self.CSS_MESSAGE_REPLY_PENDING)
            self.color_bar.setStyleSheet(self.CSS_COLOR_BAR_REPLY_PENDING)

    @pyqtSlot(str, str, str)
    def _on_reply_success(self, source_id: str, message_uuid: str, content: str) -> None:
        """
        Conditionally update this ReplyWidget's state if and only if the message_uuid of the emitted
        signal matches the uuid of this widget.
        """
        if message_uuid == self.uuid:
            self._set_reply_state('SUCCEEDED')

    @pyqtSlot(str)
    def _on_reply_failure(self, message_uuid: str) -> None:
        """
        Conditionally update this ReplyWidget's state if and only if the message_uuid of the emitted
        signal matches the uuid of this widget.
        """
        if message_uuid == self.uuid:
            self._set_reply_state('FAILED')


class FileWidget(QWidget):
    """
    Represents a file.
    """

    CSS = '''
    #file_widget {
        min-width: 540px;
        max-width: 540px;
    }
    #file_options {
        min-width: 137px;
    }
    QPushButton#export_print {
        border: none;
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
    QPushButton#download_button:hover {
        color: #05a6fe;
    }
    QLabel#file_name {
        font-family: 'Source Sans Pro';
        font-weight: 600;
        font-size: 13px;
        color: #2a319d;
    }
    QLabel#file_name:hover {
        color: #05a6fe;
    }
    QLabel#no_file_name {
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
        font-size: 13px;
        color: #2a319d;
    }
    QWidget#horizontal_line {
        min-height: 2px;
        max-height: 2px;
        background-color: rgba(211, 216, 234, 0.45);
        margin: 0px 8px 0px 8px;
    }
    '''

    download_button_css = """
    QPushButton#download_button {
        border: none;
        font-family: 'Source Sans Pro';
        font-weight: 600;
        font-size: 13px;
        color: #2a319d;
    }
    QPushButton#download_button:hover {
        color: #05a6fe;
    }
    """

    TOP_MARGIN = 4
    BOTTOM_MARGIN = 14
    FILE_FONT_SPACING = 2
    FILE_OPTIONS_FONT_SPACING = 1.6
    FILENAME_WIDTH_PX = 360
    FILE_OPTIONS_LAYOUT_SPACING = 8

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
        self.uuid = file_uuid
        self.index = index
        self.downloading = False

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
        layout.setContentsMargins(0, self.TOP_MARGIN, 0, self.BOTTOM_MARGIN)
        layout.setSpacing(0)

        # File options: download, export, print
        self.file_options = QWidget()
        self.file_options.setObjectName('file_options')
        file_options_layout = QHBoxLayout()
        self.file_options.setLayout(file_options_layout)
        file_options_layout.setContentsMargins(0, 0, 0, 0)
        file_options_layout.setSpacing(self.FILE_OPTIONS_LAYOUT_SPACING)
        file_options_layout.setAlignment(Qt.AlignLeft)
        self.download_button = QPushButton(_(' DOWNLOAD'))
        self.download_button.setObjectName('download_button')
        self.download_button.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)
        self.download_button.setIcon(load_icon('download_file.svg'))
        self.download_button.setFont(self.file_buttons_font)
        self.download_button.setCursor(QCursor(Qt.PointingHandCursor))
        self.download_button.setStyleSheet(self.download_button_css)
        self.download_animation = load_movie("download_file.gif")
        self.export_button = QPushButton(_('EXPORT'))
        self.export_button.setObjectName('export_print')
        self.export_button.setFont(self.file_buttons_font)
        self.export_button.setCursor(QCursor(Qt.PointingHandCursor))
        self.middot = QLabel("·")
        self.print_button = QPushButton(_('PRINT'))
        self.print_button.setObjectName('export_print')
        self.print_button.setFont(self.file_buttons_font)
        self.print_button.setCursor(QCursor(Qt.PointingHandCursor))
        file_options_layout.addWidget(self.download_button)
        file_options_layout.addWidget(self.export_button)
        file_options_layout.addWidget(self.middot)
        file_options_layout.addWidget(self.print_button)

        self.download_button.installEventFilter(self)
        self.export_button.clicked.connect(self._on_export_clicked)
        self.print_button.clicked.connect(self._on_print_clicked)

        self.file_name = SecureQLabel(
            wordwrap=False, max_length=self.FILENAME_WIDTH_PX, with_tooltip=True
        )
        self.file_name.setObjectName('file_name')
        self.file_name.installEventFilter(self)
        self.file_name.setCursor(QCursor(Qt.PointingHandCursor))
        self.no_file_name = SecureQLabel('ENCRYPTED FILE ON SERVER', wordwrap=False)
        self.no_file_name.setObjectName('no_file_name')
        self.no_file_name.setFont(file_description_font)

        # Line between file name and file size
        self.horizontal_line = QWidget()
        self.horizontal_line.setObjectName('horizontal_line')
        self.horizontal_line.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        # Space between elided file name and file size when horizontal line is hidden
        self.spacer = QWidget()
        self.spacer.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        self.spacer.hide()

        # File size
        self.file_size = SecureQLabel(humanize_filesize(self.file.size))
        self.file_size.setObjectName('file_size')
        self.file_size.setAlignment(Qt.AlignRight)

        # Decide what to show or hide based on whether or not the file's been downloaded
        self._set_file_state()

        # Add widgets
        layout.addWidget(self.file_options)
        layout.addWidget(self.file_name)
        layout.addWidget(self.no_file_name)
        layout.addWidget(self.horizontal_line)
        layout.addWidget(self.spacer)
        layout.addWidget(self.file_size)

        # Connect signals to slots
        file_ready_signal.connect(self._on_file_downloaded, type=Qt.QueuedConnection)
        file_missing.connect(self._on_file_missing, type=Qt.QueuedConnection)

    def update_file_size(self):
        try:
            self.file_size.setText(humanize_filesize(self.file.size))
        except Exception as e:
            logger.error(f"Could not update file size on FileWidget: {e}")
            self.file_size.setText("")

    def eventFilter(self, obj, event):
        t = event.type()
        if t == QEvent.MouseButtonPress:
            if event.button() == Qt.LeftButton:
                self._on_left_click()
        # See https://github.com/freedomofpress/securedrop-client/issues/835
        # for context on code below.
        if t == QEvent.HoverEnter and not self.downloading:
            self.download_button.setIcon(load_icon('download_file_hover.svg'))
        elif t == QEvent.HoverLeave and not self.downloading:
            self.download_button.setIcon(load_icon('download_file.svg'))
        return QObject.event(obj, event)

    def _set_file_state(self):
        if self.file.is_decrypted:
            logger.debug('Changing file {} state to decrypted/downloaded'.format(self.uuid))
            self._set_file_name()
            self.download_button.hide()
            self.no_file_name.hide()
            self.export_button.show()
            self.middot.show()
            self.print_button.show()
            self.file_name.show()
            self.update_file_size()
        else:
            logger.debug('Changing file {} state to not downloaded'.format(self.uuid))
            self.download_button.setText(_('DOWNLOAD'))
            # Ensure correct icon depending on mouse hover state.
            if self.download_button.underMouse():
                self.download_button.setIcon(load_icon('download_file_hover.svg'))
            else:
                self.download_button.setIcon(load_icon('download_file.svg'))
            self.download_button.setFont(self.file_buttons_font)
            self.download_button.show()
            self.download_button.setStyleSheet(self.download_button_css)
            self.no_file_name.hide()
            self.export_button.hide()
            self.middot.hide()
            self.print_button.hide()
            self.file_name.hide()
            self.no_file_name.show()

    def _set_file_name(self):
        self.file_name.setText(self.file.filename)
        if self.file_name.is_elided():
            self.horizontal_line.hide()
            self.spacer.show()

    @pyqtSlot(str, str, str)
    def _on_file_downloaded(self, source_uuid: str, file_uuid: str, filename: str) -> None:
        if file_uuid == self.uuid:
            self.downloading = False
            QTimer.singleShot(300, self.stop_button_animation)

    @pyqtSlot(str, str, str)
    def _on_file_missing(self, source_uuid: str, file_uuid: str, filename: str) -> None:
        if file_uuid == self.uuid:
            self.downloading = False
            QTimer.singleShot(300, self.stop_button_animation)

    @pyqtSlot()
    def _on_export_clicked(self):
        """
        Called when the export button is clicked.
        """
        if not self.controller.downloaded_file_exists(self.file):
            return

        self.export_dialog = ExportDialog(self.controller, self.uuid, self.file.filename)
        self.export_dialog.show()

    @pyqtSlot()
    def _on_print_clicked(self):
        """
        Called when the print button is clicked.
        """
        if not self.controller.downloaded_file_exists(self.file):
            return

        dialog = PrintDialog(self.controller, self.uuid, self.file.filename)
        dialog.exec()

    def _on_left_click(self):
        """
        Handle a completed click via the program logic. The download state
        of the file distinguishes which function in the logic layer to call.
        """
        # update state
        self.file = self.controller.get_file(self.uuid)

        if self.file.is_decrypted:
            # Open the already downloaded and decrypted file.
            self.controller.on_file_open(self.file)
        elif not self.downloading:
            if self.controller.api:
                self.start_button_animation()
            # Download the file.
            self.controller.on_submission_download(File, self.uuid)

    def start_button_animation(self):
        """
        Update the download button to the animated "downloading" state.
        """
        self.downloading = True
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

    def stop_button_animation(self):
        """
        Stops the download animation and restores the button to its default state.
        """
        self.download_animation.stop()
        self.file = self.controller.get_file(self.file.uuid)
        self._set_file_state()


class ModalDialog(QDialog):

    CSS = '''
    #modal {
        min-width: 800px;
        max-width: 800px;
        min-height: 300px;
        max-height: 800px;
        background-color: #fff;
    }
    #header_icon, #header_spinner {
        min-width: 80px;
        max-width: 80px;
        min-height: 64px;
        max-height: 64px;
        margin: 0px 0px 0px 30px;
    }
    #header {
        min-height: 68px;
        max-height: 68px;
        margin: 0px 0px 0px 4px;
        font-family: 'Montserrat';
        font-size: 24px;
        font-weight: 600;
        color: #2a319d;
    }
    #header_line {
        margin: 0px 40px 20px 40px;
        min-height: 2px;
        max-height: 2px;
        background-color: rgba(42, 49, 157, 0.15);
        border: none;
    }
    #error_details {
        margin: 0px 40px 0px 36px;
        font-family: 'Montserrat';
        font-size: 16px;
        color: #ff0064;
    }
    #body {
        font-family: 'Montserrat';
        font-size: 16px;
        color: #302aa3;
    }
    #button_box QPushButton {
        margin: 0px 0px 0px 12px;
        height: 40px;
        padding-left: 20px;
        padding-right: 20px;
        border: 2px solid #2a319d;
        font-family: 'Montserrat';
        font-weight: 500;
        font-size: 15px;
        color: #2a319d;
    }
    #button_box QPushButton::disabled {
        border: 2px solid rgba(42, 49, 157, 0.4);
        color: rgba(42, 49, 157, 0.4);
    }
    #button_box QPushButton#primary_button {
        background-color: #2a319d;
        color: #fff;
    }
    #button_box QPushButton#primary_button::disabled {
        border: 2px solid #C2C4E3;
        background-color: #C2C4E3;
        color: #E1E2F1;
    }
    '''

    MARGIN = 40
    NO_MARGIN = 0

    def __init__(self):
        parent = QApplication.activeWindow()
        super().__init__(parent)
        self.setObjectName('modal')
        self.setStyleSheet(self.CSS)
        self.setModal(True)

        # Header for icon and task title
        header_container = QWidget()
        header_container_layout = QHBoxLayout()
        header_container.setLayout(header_container_layout)
        self.header_icon = SvgLabel('blank.svg', svg_size=QSize(64, 64))
        self.header_icon.setObjectName('header_icon')
        self.header_spinner = QPixmap()
        self.header_spinner_label = QLabel()
        self.header_spinner_label.setObjectName("header_spinner")
        self.header_spinner_label.setMinimumSize(64, 64)
        self.header_spinner_label.setVisible(False)
        self.header_spinner_label.setPixmap(self.header_spinner)
        self.header = QLabel()
        self.header.setObjectName('header')
        header_container_layout.addWidget(self.header_icon)
        header_container_layout.addWidget(self.header_spinner_label)
        header_container_layout.addWidget(self.header, alignment=Qt.AlignCenter)
        header_container_layout.addStretch()

        self.header_line = QWidget()
        self.header_line.setObjectName('header_line')

        # Widget for displaying error messages
        self.error_details = QLabel()
        self.error_details.setObjectName('error_details')
        self.error_details.setWordWrap(True)
        self.error_details.hide()

        # Body to display instructions and forms
        self.body = QLabel()
        self.body.setObjectName('body')
        self.body.setWordWrap(True)
        self.body.setScaledContents(True)
        body_container = QWidget()
        self.body_layout = QVBoxLayout()
        self.body_layout.setContentsMargins(self.MARGIN, self.NO_MARGIN, self.MARGIN, self.MARGIN)
        body_container.setLayout(self.body_layout)
        self.body_layout.addWidget(self.body)

        # Buttons to continue and cancel
        window_buttons = QWidget()
        window_buttons.setObjectName('window_buttons')
        button_layout = QVBoxLayout()
        window_buttons.setLayout(button_layout)
        self.cancel_button = QPushButton(_('CANCEL'))
        self.cancel_button.clicked.connect(self.close)
        self.cancel_button.setAutoDefault(False)
        self.continue_button = QPushButton(_('CONTINUE'))
        self.continue_button.setObjectName('primary_button')
        self.continue_button.setDefault(True)
        self.continue_button.setIconSize(QSize(21, 21))
        button_box = QDialogButtonBox(Qt.Horizontal)
        button_box.setObjectName('button_box')
        button_box.addButton(self.cancel_button, QDialogButtonBox.ActionRole)
        button_box.addButton(self.continue_button, QDialogButtonBox.ActionRole)
        button_layout.addWidget(button_box, alignment=Qt.AlignRight)
        button_layout.setContentsMargins(self.NO_MARGIN, self.NO_MARGIN, self.MARGIN, self.MARGIN)

        # Main widget layout
        layout = QVBoxLayout(self)
        self.setLayout(layout)
        layout.addWidget(header_container)
        layout.addWidget(self.header_line)
        layout.addWidget(self.error_details)
        layout.addWidget(body_container)
        layout.addStretch()
        layout.addWidget(window_buttons)

        # Activestate animation.
        self.button_animation = load_movie("activestate-wide.gif")
        self.button_animation.setScaledSize(QSize(32, 32))
        self.button_animation.frameChanged.connect(self.animate_activestate)

        # Header animation.
        self.header_animation = load_movie("header_animation.gif")
        self.header_animation.setScaledSize(QSize(64, 64))
        self.header_animation.frameChanged.connect(self.animate_header)

    def keyPressEvent(self, event: QKeyEvent):
        if (event.key() == Qt.Key_Enter or event.key() == Qt.Key_Return):
            if self.cancel_button.hasFocus():
                self.cancel_button.click()
            else:
                self.continue_button.click()
            event.ignore()  # Don't allow Enter to close dialog

        super().keyPressEvent(event)

    def animate_activestate(self):
        self.continue_button.setIcon(QIcon(self.button_animation.currentPixmap()))

    def animate_header(self):
        self.header_spinner_label.setPixmap(self.header_animation.currentPixmap())

    def start_animate_activestate(self):
        self.button_animation.start()
        self.continue_button.setText("")
        self.continue_button.setMinimumSize(QSize(142, 43))
        css = """
        background-color: #f1f1f6;
        color: #fff;
        border: 2px solid #f1f1f6;
        margin: 0px 0px 0px 12px;
        height: 40px;
        padding-left: 20px;
        padding-right: 20px;
        """
        self.continue_button.setStyleSheet(css)
        self.error_details.setStyleSheet("color: #ff66C4")

    def start_animate_header(self):
        self.header_icon.setVisible(False)
        self.header_spinner_label.setVisible(True)
        self.header_animation.start()

    def stop_animate_activestate(self):
        self.continue_button.setIcon(QIcon())
        self.button_animation.stop()
        self.continue_button.setText(_('CONTINUE'))
        css = "background-color: #2a319d; color: #fff; border: 2px solid #2a319d;"
        self.continue_button.setStyleSheet(css)
        self.error_details.setStyleSheet("color: #ff0064")

    def stop_animate_header(self):
        self.header_icon.setVisible(True)
        self.header_spinner_label.setVisible(False)
        self.header_animation.stop()


class PrintDialog(ModalDialog):

    FILENAME_WIDTH_PX = 260

    def __init__(self, controller: Controller, file_uuid: str, file_name: str):
        super().__init__()

        self.controller = controller
        self.file_uuid = file_uuid
        self.file_name = SecureQLabel(
            file_name, wordwrap=False, max_length=self.FILENAME_WIDTH_PX).text()
        self.error_status = ''  # Hold onto the error status we receive from the Export VM

        # Connect controller signals to slots
        self.controller.export.printer_preflight_success.connect(self._on_preflight_success)
        self.controller.export.printer_preflight_failure.connect(self._on_preflight_failure)

        # Connect parent signals to slots
        self.continue_button.setEnabled(False)
        self.continue_button.clicked.connect(self._run_preflight)

        # Dialog content
        self.starting_header = _(
            'Preparing to print:'
            '<br />'
            '<span style="font-weight:normal">{}</span>'.format(self.file_name))
        self.ready_header = _(
            'Ready to print:'
            '<br />'
            '<span style="font-weight:normal">{}</span>'.format(self.file_name))
        self.insert_usb_header = _('Connect USB printer')
        self.error_header = _('Printing failed')
        self.starting_message = _(
            '<h2>Managing printout risks</h2>'
            '<b>QR codes and web addresses</b>'
            '<br />'
            'Never type in and open web addresses or scan QR codes contained in printed '
            'documents without taking security precautions. If you are unsure how to '
            'manage this risk, please contact your administrator.'
            '<br /><br />'
            '<b>Printer dots</b>'
            '<br />'
            'Any part of a printed page may contain identifying information '
            'invisible to the naked eye, such as printer dots. Please carefully '
            'consider this risk when working with or publishing scanned printouts.')
        self.insert_usb_message = _('Please connect your printer to a USB port.')
        self.generic_error_message = _('See your administrator for help.')

        self._show_starting_instructions()
        self.start_animate_header()
        self._run_preflight()

    def _show_starting_instructions(self):
        self.header.setText(self.starting_header)
        self.body.setText(self.starting_message)
        self.error_details.hide()
        self.adjustSize()

    def _show_insert_usb_message(self):
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self._run_preflight)
        self.header.setText(self.insert_usb_header)
        self.body.setText(self.insert_usb_message)
        self.error_details.hide()
        self.adjustSize()

    def _show_generic_error_message(self):
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self.close)
        self.continue_button.setText('DONE')
        self.header.setText(self.error_header)
        self.body.setText('{}: {}'.format(self.error_status, self.generic_error_message))
        self.error_details.hide()
        self.adjustSize()

    @pyqtSlot()
    def _run_preflight(self):
        self.controller.run_printer_preflight_checks()

    @pyqtSlot()
    def _print_file(self):
        self.controller.print_file(self.file_uuid)
        self.close()

    @pyqtSlot()
    def _on_preflight_success(self):
        # If the continue button is disabled then this is the result of a background preflight check
        self.stop_animate_header()
        self.header_icon.update_image('printer.svg', svg_size=QSize(64, 64))
        self.header.setText(self.ready_header)
        if not self.continue_button.isEnabled():
            self.continue_button.clicked.disconnect()
            self.continue_button.clicked.connect(self._print_file)
            self.continue_button.setEnabled(True)
            self.continue_button.setFocus()
            return

        self._print_file()

    @pyqtSlot(object)
    def _on_preflight_failure(self, error: ExportError):
        self.stop_animate_header()
        self.header_icon.update_image('printer.svg', svg_size=QSize(64, 64))
        self.error_status = error.status
        # If the continue button is disabled then this is the result of a background preflight check
        if not self.continue_button.isEnabled():
            self.continue_button.clicked.disconnect()
            if error.status == ExportStatus.PRINTER_NOT_FOUND.value:
                self.continue_button.clicked.connect(self._show_insert_usb_message)
            else:
                self.continue_button.clicked.connect(self._show_generic_error_message)

            self.continue_button.setEnabled(True)
            self.continue_button.setFocus()
        else:
            if error.status == ExportStatus.PRINTER_NOT_FOUND.value:
                self._show_insert_usb_message()
            else:
                self._show_generic_error_message()


class ExportDialog(ModalDialog):

    PASSPHRASE_FORM_CSS = '''
    #passphrase_form QLabel {
        font-family: 'Montserrat';
        font-weight: 500;
        font-size: 12px;
        color: #2a319d;
        padding-top: 6px;
    }
    #passphrase_form QLineEdit {
        border-radius: 0px;
        min-height: 30px;
        max-height: 30px;
        background-color: #f8f8f8;
        padding-bottom: 2px;
    }
    '''

    PASSPHRASE_LABEL_SPACING = 0.5
    NO_MARGIN = 0
    FILENAME_WIDTH_PX = 260

    def __init__(self, controller: Controller, file_uuid: str, file_name: str):
        super().__init__()

        self.controller = controller
        self.file_uuid = file_uuid
        self.file_name = SecureQLabel(
            file_name, wordwrap=False, max_length=self.FILENAME_WIDTH_PX).text()
        self.error_status = ''  # Hold onto the error status we receive from the Export VM

        # Connect controller signals to slots
        self.controller.export.preflight_check_call_success.connect(self._on_preflight_success)
        self.controller.export.preflight_check_call_failure.connect(self._on_preflight_failure)
        self.controller.export.export_usb_call_success.connect(self._on_export_success)
        self.controller.export.export_usb_call_failure.connect(self._on_export_failure)

        # Connect parent signals to slots
        self.continue_button.setEnabled(False)
        self.continue_button.clicked.connect(self._run_preflight)

        # Dialog content
        self.starting_header = _(
            'Preparing to export:'
            '<br />'
            '<span style="font-weight:normal">{}</span>'.format(self.file_name))
        self.ready_header = _(
            'Ready to export:'
            '<br />'
            '<span style="font-weight:normal">{}</span>'.format(self.file_name))
        self.insert_usb_header = _('Insert encrypted USB drive')
        self.passphrase_header = _('Enter passphrase for USB drive')
        self.success_header = _('Export successful')
        self.error_header = _('Export failed')
        self.starting_message = _(
            '<h2>Understand the risks before exporting files</h2>'
            '<b>Malware</b>'
            '<br />'
            'This workstation lets you open files securely. If you open files on another '
            'computer, any embedded malware may spread to your computer or network. If you are '
            'unsure how to manage this risk, please print the file, or contact your '
            'administrator.'
            '<br /><br />'
            '<b>Anonymity</b>'
            '<br />'
            'Files submitted by sources may contain information or hidden metadata that '
            'identifies who they are. To protect your sources, please consider redacting files '
            'before working with them on network-connected computers.')
        self.exporting_message = _('Exporting: {}'.format(self.file_name))
        self.insert_usb_message = _(
            'Please insert one of the export drives provisioned specifically '
            'for the SecureDrop Workstation.')
        self.usb_error_message = _(
            'Either the drive is not encrypted or there is something else wrong with it.')
        self.passphrase_error_message = _('The passphrase provided did not work. Please try again.')
        self.generic_error_message = _('See your administrator for help.')
        self.continue_disabled_message = _(
            'The CONTINUE button will be disabled until the Export VM is ready')
        self.success_message = _(
            'Remember to be careful when working with files outside of your Workstation machine.')

        # Passphrase Form
        self.passphrase_form = QWidget()
        self.passphrase_form.setStyleSheet(self.PASSPHRASE_FORM_CSS)
        self.passphrase_form.setObjectName('passphrase_form')
        passphrase_form_layout = QVBoxLayout()
        passphrase_form_layout.setContentsMargins(
            self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN)
        self.passphrase_form.setLayout(passphrase_form_layout)
        passphrase_label = SecureQLabel(_('Passphrase'))
        passphrase_label.setObjectName('passphrase_label')
        font = QFont()
        font.setLetterSpacing(QFont.AbsoluteSpacing, self.PASSPHRASE_LABEL_SPACING)
        passphrase_label.setFont(font)
        self.passphrase_field = PasswordEdit(self)
        self.passphrase_field.setEchoMode(QLineEdit.Password)
        effect = QGraphicsDropShadowEffect(self)
        effect.setOffset(0, -1)
        effect.setBlurRadius(4)
        effect.setColor(QColor('#aaa'))
        self.passphrase_field.setGraphicsEffect(effect)
        passphrase_form_layout.addWidget(passphrase_label)
        passphrase_form_layout.addWidget(self.passphrase_field)
        self.body_layout.addWidget(self.passphrase_form)
        self.passphrase_form.hide()

        self._show_starting_instructions()
        self.start_animate_header()
        self._run_preflight()

    def _show_starting_instructions(self):
        self.header.setText(self.starting_header)
        self.body.setText(self.starting_message)
        self.adjustSize()

    def _show_passphrase_request_message(self):
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self._export_file)
        self.header.setText(self.passphrase_header)
        self.continue_button.setText('SUBMIT')
        self.header_line.hide()
        self.error_details.hide()
        self.body.hide()
        self.passphrase_field.setFocus()
        self.passphrase_form.show()
        self.adjustSize()

    def _show_passphrase_request_message_again(self):
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self._export_file)
        self.header.setText(self.passphrase_header)
        self.error_details.setText(self.passphrase_error_message)
        self.continue_button.setText('SUBMIT')
        self.header_line.hide()
        self.body.hide()
        self.error_details.show()
        self.passphrase_field.setFocus()
        self.passphrase_form.show()
        self.adjustSize()

    def _show_success_message(self):
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self.close)
        self.header.setText(self.success_header)
        self.continue_button.setText('DONE')
        self.body.setText(self.success_message)
        self.cancel_button.hide()
        self.error_details.hide()
        self.passphrase_form.hide()
        self.header_line.show()
        self.body.show()
        self.adjustSize()

    def _show_insert_usb_message(self):
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self._run_preflight)
        self.header.setText(self.insert_usb_header)
        self.continue_button.setText('CONTINUE')
        self.body.setText(self.insert_usb_message)
        self.error_details.hide()
        self.passphrase_form.hide()
        self.header_line.show()
        self.body.show()
        self.adjustSize()

    def _show_insert_encrypted_usb_message(self):
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self._run_preflight)
        self.header.setText(self.insert_usb_header)
        self.error_details.setText(self.usb_error_message)
        self.continue_button.setText('CONTINUE')
        self.body.setText(self.insert_usb_message)
        self.passphrase_form.hide()
        self.header_line.show()
        self.error_details.show()
        self.body.show()
        self.adjustSize()

    def _show_generic_error_message(self):
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self.close)
        self.continue_button.setText('DONE')
        self.header.setText(self.error_header)
        self.body.setText('{}: {}'.format(self.error_status, self.generic_error_message))
        self.error_details.hide()
        self.passphrase_form.hide()
        self.header_line.show()
        self.body.show()
        self.adjustSize()

    @pyqtSlot()
    def _run_preflight(self):
        self.controller.run_export_preflight_checks()

    @pyqtSlot()
    def _export_file(self, checked: bool = False):
        self.start_animate_activestate()
        self.cancel_button.setEnabled(False)
        self.passphrase_field.setDisabled(True)
        self.controller.export_file_to_usb_drive(self.file_uuid, self.passphrase_field.text())

    @pyqtSlot()
    def _on_preflight_success(self):
        # If the continue button is disabled then this is the result of a background preflight check
        self.stop_animate_header()
        self.header_icon.update_image('savetodisk.svg', QSize(64, 64))
        self.header.setText(self.ready_header)
        if not self.continue_button.isEnabled():
            self.continue_button.clicked.disconnect()
            self.continue_button.clicked.connect(self._show_passphrase_request_message)
            self.continue_button.setEnabled(True)
            self.continue_button.setFocus()
            return

        self._show_passphrase_request_message()

    @pyqtSlot(object)
    def _on_preflight_failure(self, error: ExportError):
        self.stop_animate_header()
        self.header_icon.update_image('savetodisk.svg', QSize(64, 64))
        self._update_dialog(error.status)

    @pyqtSlot()
    def _on_export_success(self):
        self.stop_animate_activestate()
        self._show_success_message()

    @pyqtSlot(object)
    def _on_export_failure(self, error: ExportError):
        self.stop_animate_activestate()
        self.cancel_button.setEnabled(True)
        self.passphrase_field.setDisabled(False)
        self._update_dialog(error.status)

    def _update_dialog(self, error_status: str):
        self.error_status = error_status
        # If the continue button is disabled then this is the result of a background preflight check
        if not self.continue_button.isEnabled():
            self.continue_button.clicked.disconnect()
            if self.error_status == ExportStatus.BAD_PASSPHRASE.value:
                self.continue_button.clicked.connect(self._show_passphrase_request_message_again)
            elif self.error_status == ExportStatus.USB_NOT_CONNECTED.value:
                self.continue_button.clicked.connect(self._show_insert_usb_message)
            elif self.error_status == ExportStatus.DISK_ENCRYPTION_NOT_SUPPORTED_ERROR.value:
                self.continue_button.clicked.connect(self._show_insert_encrypted_usb_message)
            else:
                self.continue_button.clicked.connect(self._show_generic_error_message)

            self.continue_button.setEnabled(True)
            self.continue_button.setFocus()
        else:
            if self.error_status == ExportStatus.BAD_PASSPHRASE.value:
                self._show_passphrase_request_message_again()
            elif self.error_status == ExportStatus.USB_NOT_CONNECTED.value:
                self._show_insert_usb_message()
            elif self.error_status == ExportStatus.DISK_ENCRYPTION_NOT_SUPPORTED_ERROR.value:
                self._show_insert_encrypted_usb_message()
            else:
                self._show_generic_error_message()


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
        self.source_uuid = self.source.uuid
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
        # source collection and should be removed from both the layout and the conversation
        # dict. Note that an item may be removed from the source collection if it is deleted
        # by another user (a journalist using the Web UI is able to delete individual
        # submissions).
        for item_widget in current_conversation.values():
            logger.debug('Deleting item: {}'.format(item_widget.uuid))
            self.current_messages.pop(item_widget.uuid)
            item_widget.deleteLater()
            self.conversation_layout.removeWidget(item_widget)

    def add_file(self, file: File, index):
        """
        Add a file from the source.
        """
        logger.debug('Adding file for {}'.format(file.uuid))
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

    SOURCE_DELETED_CSS = '''
    #source_deleted {
        text-align: left;
        font-family: 'Montserrat';
        font-weight: 500;
        font-size: 40px;
        color: #a5b3e9;
        padding-bottom: 264px;
        padding-right: 195px;
    }
    '''

    def __init__(self, source: Source, controller: Controller) -> None:
        super().__init__()

        self.source_uuid = source.uuid
        controller.source_deleted.connect(self._on_source_deleted)
        controller.source_deletion_failed.connect(self._on_source_deletion_failed)

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
        self.waiting_delete_confirmation = QLabel('Deleting...')
        self.waiting_delete_confirmation.setObjectName('source_deleted')
        self.waiting_delete_confirmation.setStyleSheet(self.SOURCE_DELETED_CSS)
        self.waiting_delete_confirmation.hide()

        # Add widgets
        layout.addWidget(self.conversation_title_bar)
        layout.addWidget(self.conversation_view)
        layout.addWidget(self.reply_box)
        layout.addWidget(self.waiting_delete_confirmation, alignment=Qt.AlignCenter)

        # Connect reply_box to conversation_view
        self.reply_box.reply_sent.connect(self.conversation_view.on_reply_sent)
        self.conversation_view.conversation_updated.connect(
            self.conversation_title_bar.update_timestamp)

    @pyqtSlot(str)
    def _on_source_deleted(self, source_uuid: str):
        if self.source_uuid == source_uuid:
            self.conversation_title_bar.hide()
            self.conversation_view.hide()
            self.reply_box.hide()
            self.waiting_delete_confirmation.show()

    @pyqtSlot(str)
    def _on_source_deletion_failed(self, source_uuid: str):
        if self.source_uuid == source_uuid:
            self.waiting_delete_confirmation.hide()
            self.conversation_title_bar.show()
            self.conversation_view.show()
            self.reply_box.show()


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

        # Determine whether or not this widget should be rendered in offline mode
        self.update_authentication_state(self.controller.is_authenticated)

        # Text area refocus flag.
        self.refocus_after_sync = False

        # Connect signals to slots
        self.controller.authentication_state.connect(self._on_authentication_changed)
        self.controller.sync_events.connect(self._on_synced)

    def set_logged_in(self):
        self.text_edit.set_logged_in()
        # Even if we are logged in, we cannot reply to a source if we do not
        # have a public key for it.
        if self.source.public_key:
            self.replybox.setEnabled(True)
            self.send_button.show()
        else:
            self.replybox.setEnabled(False)
            self.send_button.hide()

    def set_logged_out(self):
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
        try:
            self.update_authentication_state(authenticated)
        except sqlalchemy.orm.exc.ObjectDeletedError:
            logger.debug(
                "On authentication change, ReplyBoxWidget found its source had been deleted."
            )
            self.destroy()

    def update_authentication_state(self, authenticated: bool) -> None:
        if authenticated:
            self.set_logged_in()
        else:
            self.set_logged_out()

    def _on_synced(self, data: str) -> None:
        try:
            self.update_authentication_state(self.controller.is_authenticated)

            if data == 'syncing' and self.text_edit.hasFocus():
                self.refocus_after_sync = True
            elif data == 'synced' and self.refocus_after_sync:
                self.text_edit.setFocus()
            else:
                self.refocus_after_sync = False
        except sqlalchemy.orm.exc.ObjectDeletedError:
            logger.debug("During sync, ReplyBoxWidget found its source had been deleted.")
            self.destroy()


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
            msg = "<strong><font color=\"#24276d\">Awaiting encryption key</font></strong>"
            placeholder = msg + " from the server to enable replies."
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
