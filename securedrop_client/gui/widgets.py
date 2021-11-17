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
import html
import logging
from gettext import gettext as _
from gettext import ngettext
from typing import Dict, List, Optional, Union  # noqa: F401
from uuid import uuid4

import arrow
import sqlalchemy.orm.exc
from PyQt5.QtCore import QEvent, QObject, QSize, Qt, QTimer, pyqtBoundSignal, pyqtSignal, pyqtSlot
from PyQt5.QtGui import (
    QBrush,
    QColor,
    QCursor,
    QFocusEvent,
    QFont,
    QIcon,
    QKeyEvent,
    QKeySequence,
    QLinearGradient,
    QMouseEvent,
    QPalette,
    QPixmap,
    QResizeEvent,
)
from PyQt5.QtWidgets import (
    QAction,
    QApplication,
    QDialog,
    QDialogButtonBox,
    QGraphicsDropShadowEffect,
    QGridLayout,
    QHBoxLayout,
    QLabel,
    QLineEdit,
    QListWidget,
    QListWidgetItem,
    QMenu,
    QPlainTextEdit,
    QPushButton,
    QScrollArea,
    QSizePolicy,
    QSpacerItem,
    QStatusBar,
    QToolButton,
    QVBoxLayout,
    QWidget,
)

from securedrop_client.db import (
    DraftReply,
    File,
    Message,
    Reply,
    ReplySendStatusCodes,
    Source,
    User,
)
from securedrop_client.export import ExportError, ExportStatus
from securedrop_client.gui import (
    SDPushButton,
    SecureQLabel,
    SvgLabel,
    SvgPushButton,
    SvgToggleButton,
)
from securedrop_client.logic import Controller
from securedrop_client.resources import load_css, load_icon, load_image, load_movie
from securedrop_client.storage import source_exists
from securedrop_client.utils import humanize_filesize

logger = logging.getLogger(__name__)


class TopPane(QWidget):
    """
    Top pane of the app window.
    """

    def __init__(self) -> None:
        super().__init__()

        # Fill the background with a gradient
        self.online_palette = QPalette()
        gradient = QLinearGradient(0, 0, 1553, 0)
        gradient.setColorAt(0, QColor("#1573d8"))
        gradient.setColorAt(0.22, QColor("#0060d3"))
        gradient.setColorAt(1, QColor("#002c53"))
        self.online_palette.setBrush(QPalette.Background, QBrush(gradient))

        self.offline_palette = QPalette()
        gradient = QLinearGradient(0, 0, 1553, 0)
        gradient.setColorAt(0, QColor("#1e1e1e"))
        gradient.setColorAt(0.22, QColor("#122d61"))
        gradient.setColorAt(1, QColor("#0d4a81"))
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

    def setup(self, controller: Controller) -> None:
        self.sync_icon.setup(controller)
        self.error_status_bar.setup(controller)

    def set_logged_in(self) -> None:
        self.sync_icon.enable()
        self.setPalette(self.online_palette)

    def set_logged_out(self) -> None:
        self.sync_icon.disable()
        self.setPalette(self.offline_palette)

    def update_activity_status(self, message: str, duration: int) -> None:
        self.activity_status_bar.update_message(message, duration)

    def update_error_status(self, message: str, duration: int) -> None:
        self.error_status_bar.update_message(message, duration)

    def clear_error_status(self) -> None:
        self.error_status_bar.clear_message()


class LeftPane(QWidget):
    """
    Represents the left side pane that contains user authentication actions and information.
    """

    def __init__(self) -> None:
        super().__init__()

        self.setObjectName("LeftPane")

        # Set layout
        layout = QVBoxLayout(self)
        self.setLayout(layout)

        # Remove margins and spacing
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        self.branding_barre = QLabel()
        self.branding_barre.setPixmap(load_image("left_pane.svg"))
        self.user_profile = UserProfile()

        # Hide user profile widget until user logs in
        self.user_profile.hide()

        # Add widgets to layout
        layout.addWidget(self.user_profile)
        layout.addWidget(self.branding_barre)

    def setup(self, window, controller: Controller) -> None:  # type: ignore [no-untyped-def]
        self.user_profile.setup(window, controller)

    def set_logged_in_as(self, db_user: User) -> None:
        """
        Update the UI to reflect that the user is logged in as "username".
        """
        self.user_profile.set_user(db_user)
        self.user_profile.show()
        self.branding_barre.setPixmap(load_image("left_pane.svg"))

    def set_logged_out(self) -> None:
        """
        Update the UI to a logged out state.
        """
        self.user_profile.hide()
        self.branding_barre.setPixmap(load_image("left_pane_offline.svg"))


class SyncIcon(QLabel):
    """
    An icon that shows sync state.
    """

    def __init__(self) -> None:
        # Add svg images to button
        super().__init__()
        self.setObjectName("SyncIcon")
        self.setFixedSize(QSize(24, 20))
        self.sync_animation = load_movie("sync_disabled.gif")
        self.sync_animation.setScaledSize(QSize(24, 20))
        self.setMovie(self.sync_animation)
        self.sync_animation.start()

    def setup(self, controller: Controller) -> None:
        """
        Assign a controller object (containing the application logic).
        """
        self.controller = controller
        self.controller.sync_events.connect(self._on_sync)

    def _on_sync(self, data) -> None:  # type: ignore [no-untyped-def]
        if data == "syncing":
            self.sync_animation = load_movie("sync_active.gif")
            self.sync_animation.setScaledSize(QSize(24, 20))
            self.setMovie(self.sync_animation)
            self.sync_animation.start()
        elif data == "synced":
            self.sync_animation = load_movie("sync.gif")
            self.sync_animation.setScaledSize(QSize(24, 20))
            self.setMovie(self.sync_animation)
            self.sync_animation.start()

    def enable(self) -> None:
        self.sync_animation = load_movie("sync.gif")
        self.sync_animation.setScaledSize(QSize(24, 20))
        self.setMovie(self.sync_animation)
        self.sync_animation.start()

    def disable(self) -> None:
        self.sync_animation = load_movie("sync_disabled.gif")
        self.sync_animation.setScaledSize(QSize(24, 20))
        self.setMovie(self.sync_animation)
        self.sync_animation.start()


class ActivityStatusBar(QStatusBar):
    """
    A status bar for displaying messages about application activity to the user. Messages will be
    displayed for a given duration or until the message updated with a new message.
    """

    def __init__(self) -> None:
        super().__init__()

        # Set css id
        self.setObjectName("ActivityStatusBar")

        # Remove grip image at bottom right-hand corner
        self.setSizeGripEnabled(False)

    def update_message(self, message: str, duration: int) -> None:
        """
        Display a status message to the user.
        """
        self.showMessage(message, duration)


class ErrorStatusBar(QWidget):
    """
    A pop-up status bar for displaying messages about application errors to the user. Messages will
    be displayed for a given duration or until the message is cleared or updated with a new message.
    """

    def __init__(self) -> None:
        super().__init__()

        # Set layout
        layout = QHBoxLayout(self)
        self.setLayout(layout)

        # Remove margins and spacing
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Error vertical bar
        self.vertical_bar = QWidget()
        self.vertical_bar.setObjectName("ErrorStatusBar_vertical_bar")  # Set css id
        self.vertical_bar.setFixedWidth(10)

        # Error icon
        self.label = SvgLabel("error_icon.svg", svg_size=QSize(20, 20))
        self.label.setObjectName("ErrorStatusBar_icon")  # Set css id
        self.label.setFixedWidth(42)

        # Error status bar
        self.status_bar = QStatusBar()
        self.status_bar.setObjectName("ErrorStatusBar_status_bar")  # Set css id
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

    def _hide(self) -> None:
        self.vertical_bar.hide()
        self.label.hide()
        self.status_bar.hide()

    def _show(self) -> None:
        self.vertical_bar.show()
        self.label.show()
        self.status_bar.show()

    def _on_status_timeout(self) -> None:
        self._hide()

    def setup(self, controller: Controller) -> None:
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

    def clear_message(self) -> None:
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

    def __init__(self) -> None:
        super().__init__()

        # Set css id
        self.setObjectName("UserProfile")

        # Set background
        palette = QPalette()
        palette.setBrush(
            QPalette.Background, QBrush(Qt.NoBrush)
        )  # This makes the widget transparent
        self.setPalette(palette)
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)

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
        self.user_icon.setObjectName("UserProfile_icon")  # Set css id
        self.user_icon.setFixedSize(QSize(30, 30))
        self.user_icon.setAlignment(Qt.AlignCenter)
        self.user_icon_font = QFont()
        self.user_icon_font.setLetterSpacing(QFont.AbsoluteSpacing, 0.58)
        self.user_icon.setFont(self.user_icon_font)
        self.user_icon.clicked.connect(self.user_button.click)
        self.user_icon.setCursor(QCursor(Qt.PointingHandCursor))

        # Add widgets to user auth layout
        layout.addWidget(self.login_button, alignment=Qt.AlignTop)
        layout.addWidget(self.user_icon, alignment=Qt.AlignTop)
        layout.addWidget(self.user_button, alignment=Qt.AlignTop)

    def setup(self, window, controller: Controller) -> None:  # type: ignore [no-untyped-def]
        self.controller = controller
        self.controller.update_authenticated_user.connect(self._on_update_authenticated_user)
        self.user_button.setup(controller)
        self.login_button.setup(window)

    @pyqtSlot(User)
    def _on_update_authenticated_user(self, db_user: User) -> None:
        self.set_user(db_user)

    def set_user(self, db_user: User) -> None:
        self.user_icon.setText(_(db_user.initials))
        self.user_button.set_username(_(db_user.fullname))

    def show(self) -> None:
        self.login_button.hide()
        self.user_icon.show()
        self.user_button.show()

    def hide(self) -> None:
        self.user_icon.hide()
        self.user_button.hide()
        self.login_button.show()


class UserIconLabel(QLabel):
    """
    Makes a label clickable. (For the label containing the user icon.)
    """

    clicked = pyqtSignal()

    def mousePressEvent(self, e: QMouseEvent) -> None:
        self.clicked.emit()


class UserButton(SvgPushButton):
    """An menu button for the journalist menu

    This button is responsible for launching the journalist menu on click.
    """

    def __init__(self) -> None:
        super().__init__("dropdown_arrow.svg", svg_size=QSize(9, 6))

        # Set css id
        self.setObjectName("UserButton")

        self.setFixedHeight(30)

        self.setLayoutDirection(Qt.RightToLeft)

        self.menu = UserMenu()
        self.setMenu(self.menu)

        # Set cursor.
        self.setCursor(QCursor(Qt.PointingHandCursor))

    def setup(self, controller: Controller) -> None:
        self.menu.setup(controller)

    def set_username(self, username: str) -> None:
        formatted_name = _("{}").format(html.escape(username))
        self.setText(formatted_name)
        if len(formatted_name) > 21:
            # The name will be truncated, so create a tooltip to display full
            # name if the mouse hovers over the widget.
            self.setToolTip(_("{}").format(html.escape(username)))


class UserMenu(QMenu):
    """A menu next to the journalist username.

    A menu that provides login options.
    """

    def __init__(self) -> None:
        super().__init__()
        self.logout = QAction(_("SIGN OUT"))
        self.logout.setFont(QFont("OpenSans", 10))
        self.addAction(self.logout)
        self.logout.triggered.connect(self._on_logout_triggered)

    def setup(self, controller: Controller) -> None:
        """
        Store a reference to the controller (containing the application logic).
        """
        self.controller = controller

    def _on_logout_triggered(self) -> None:
        """
        Called when the logout button is selected from the menu.
        """
        self.controller.logout()


class LoginButton(QPushButton):
    """
    A button that opens a login dialog when clicked.
    """

    def __init__(self) -> None:
        super().__init__(_("SIGN IN"))

        # Set css id
        self.setObjectName("LoginButton")

        self.setFixedHeight(40)

        # Set click handler
        self.clicked.connect(self._on_clicked)

    def setup(self, window) -> None:  # type: ignore [no-untyped-def]
        """
        Store a reference to the GUI window object.
        """
        self.window = window

    def _on_clicked(self) -> None:
        """
        Called when the login button is clicked.
        """
        self.window.show_login()


class MainView(QWidget):
    """
    Represents the main content of the application (containing the source list
    and main context view).
    """

    def __init__(self, parent: QObject) -> None:
        super().__init__(parent)

        # Set id and styles
        self.setObjectName("MainView")

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
        self.view_holder.setObjectName("MainView_view_holder")
        self.view_layout = QVBoxLayout()
        self.view_holder.setLayout(self.view_layout)
        self.view_layout.setContentsMargins(0, 0, 0, 0)
        self.view_layout.setSpacing(0)
        self.empty_conversation_view = EmptyConversationView()
        self.view_layout.addWidget(self.empty_conversation_view)

        # Add widgets to layout
        self.layout.addWidget(self.source_list, stretch=1)
        self.layout.addWidget(self.view_holder, stretch=2)

        # Note: We should not delete SourceConversationWrapper when its source is unselected. This
        # is a temporary solution to keep copies of our objects since we do delete them.
        self.source_conversations = {}  # type: Dict[str, SourceConversationWrapper]

    def setup(self, controller: Controller) -> None:
        """
        Pass through the controller object to this widget.
        """
        self.controller = controller
        self.source_list.setup(controller)

    def show_sources(self, sources: List[Source]) -> None:
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

        if self.source_list.source_items:
            # The source list already contains sources.
            deleted_sources = self.source_list.update(sources)
            for source_uuid in deleted_sources:
                # Then call the function to remove the wrapper and its children.
                self.delete_conversation(source_uuid)
        else:
            # We have an empty source list, so do an initial update.
            self.source_list.initial_update(sources)

    def on_source_changed(self) -> None:
        """
        Show conversation for the selected source.
        """
        try:
            source = self.source_list.get_selected_source()
            if not source:
                return

            self.controller.session.refresh(source)

            # Immediately show the selected source as seen in the UI and then make a request to mark
            # source as seen.
            self.source_list.source_selected.emit(source.uuid)
            self.controller.mark_seen(source)

            # Get or create the SourceConversationWrapper
            if source.uuid in self.source_conversations:
                conversation_wrapper = self.source_conversations[source.uuid]
                conversation_wrapper.conversation_view.update_conversation(source.collection)
            else:
                conversation_wrapper = SourceConversationWrapper(source, self.controller)
                self.source_conversations[source.uuid] = conversation_wrapper

            self.set_conversation(conversation_wrapper)
            logger.debug(
                "Set conversation to the selected source with uuid: {}".format(source.uuid)
            )
        except sqlalchemy.exc.InvalidRequestError as e:
            logger.debug(e)

    def refresh_source_conversations(self) -> None:
        deleting_conversations = [
            c for c in self.source_conversations.values() if c.deleting_conversation
        ]
        for conversation_wrapper in deleting_conversations:
            conversation_wrapper.end_conversation_deletion()

        source = self.source_list.get_selected_source()
        if not source:
            return

        self.on_source_changed()
        conversation_wrapper = self.source_conversations[source.uuid]
        source_widget = self.source_list.get_source_widget(source.uuid)
        if source_widget:
            source_widget.deletion_indicator.stop()
        try:
            conversation_wrapper.conversation_view.update_conversation(source.collection)
        except sqlalchemy.exc.InvalidRequestError as e:
            logger.debug("Error refreshing source conversations: %s", e)

    def delete_conversation(self, source_uuid: str) -> None:
        """
        When we delete a source, we should delete its SourceConversationWrapper,
        and remove the reference to it in self.source_conversations
        """
        try:
            logger.debug("Deleting SourceConversationWrapper for {}".format(source_uuid))
            conversation_wrapper = self.source_conversations[source_uuid]
            conversation_wrapper.deleteLater()
            del self.source_conversations[source_uuid]
        except KeyError:
            logger.debug("No SourceConversationWrapper for {} to delete".format(source_uuid))

    def set_conversation(self, widget: QWidget) -> None:
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


class SourceListWidgetItem(QListWidgetItem):
    def __lt__(self, other: "SourceListWidgetItem") -> bool:
        """
        Used for ordering widgets by timestamp of last interaction.
        """
        lw = self.listWidget()
        me = lw.itemWidget(self)
        them = lw.itemWidget(other)
        if me and them:
            my_ts = arrow.get(me.last_updated)
            other_ts = arrow.get(them.last_updated)
            return my_ts < other_ts
        return True


class SourceList(QListWidget):
    """
    Displays the list of sources.
    """

    NUM_SOURCES_TO_ADD_AT_A_TIME = 32
    INITIAL_UPDATE_SCROLLBAR_WIDTH = 20

    source_selected = pyqtSignal(str)
    adjust_preview = pyqtSignal(int)

    def __init__(self) -> None:
        super().__init__()

        self.setObjectName("SourceList")
        self.setUniformItemSizes(True)

        # Set layout.
        layout = QVBoxLayout(self)
        self.setLayout(layout)

        # Disable horizontal scrollbar for SourceList widget
        self.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)

        # Enable ordering.
        self.setSortingEnabled(True)

        # To hold references to SourceListWidgetItem instances indexed by source UUID.
        self.source_items: Dict[str, SourceListWidgetItem] = {}

    def resizeEvent(self, event: QResizeEvent) -> None:
        self.adjust_preview.emit(event.size().width())
        super().resizeEvent(event)

    def setup(self, controller: Controller) -> None:
        self.controller = controller
        self.controller.reply_succeeded.connect(self.set_snippet)
        self.controller.message_ready.connect(self.set_snippet)
        self.controller.reply_ready.connect(self.set_snippet)
        self.controller.file_ready.connect(self.set_snippet)
        self.controller.file_missing.connect(self.set_snippet)
        self.controller.message_download_failed.connect(self.set_snippet)
        self.controller.reply_download_failed.connect(self.set_snippet)

    def update(self, sources: List[Source]) -> List[str]:
        """
        Update the list with the passed in list of sources.
        """
        sources_to_update = []
        sources_to_add = {}
        for source in sources:
            try:
                if source.uuid in self.source_items:
                    sources_to_update.append(source.uuid)
                else:
                    sources_to_add[source.uuid] = source
            except sqlalchemy.exc.InvalidRequestError as e:
                logger.debug(e)
                continue

        # Delete widgets for sources not in the supplied sourcelist
        deleted_uuids = []
        sources_to_delete = [
            self.source_items[uuid] for uuid in self.source_items if uuid not in sources_to_update
        ]
        for source_item in sources_to_delete:
            if source_item.isSelected():
                self.setCurrentItem(None)

            source_widget = self.itemWidget(source_item)
            self.takeItem(self.row(source_item))
            if source_widget.source_uuid in self.source_items:
                del self.source_items[source_widget.source_uuid]

            deleted_uuids.append(source_widget.source_uuid)
            source_widget.deleteLater()

        # Update the remaining widgets
        for i in range(self.count()):
            source_widget = self.itemWidget(self.item(i))

            if not source_widget:
                continue

            source_widget.update()

        # Add widgets for new sources
        for uuid in sources_to_add:
            source_widget = SourceWidget(
                self.controller, sources_to_add[uuid], self.source_selected, self.adjust_preview
            )
            source_item = SourceListWidgetItem(self)
            source_item.setSizeHint(source_widget.sizeHint())
            self.insertItem(0, source_item)
            self.setItemWidget(source_item, source_widget)
            self.source_items[uuid] = source_item
            self.adjust_preview.emit(self.width() - self.INITIAL_UPDATE_SCROLLBAR_WIDTH)

        # Re-sort SourceList to make sure the most recently-updated sources appear at the top
        self.sortItems(Qt.DescendingOrder)

        # Return uuids of source widgets that were deleted so we can later delete the corresponding
        # conversation widgets
        return deleted_uuids

    def initial_update(self, sources: List[Source]) -> None:
        """
        Initialise the list with the passed in list of sources.
        """
        self.add_source(sources)

    def add_source(self, sources: List[Source], slice_size: int = 1) -> None:
        """
        Add a slice of sources, and if necessary, reschedule the addition of
        more sources.
        """

        def schedule_source_management(slice_size: int = slice_size) -> None:
            if not sources:
                self.adjust_preview.emit(self.width() - self.INITIAL_UPDATE_SCROLLBAR_WIDTH)
                return

            # Process the remaining "slice_size" number of sources.
            sources_slice = sources[:slice_size]
            for source in sources_slice:
                try:
                    source_uuid = source.uuid
                    source_widget = SourceWidget(
                        self.controller, source, self.source_selected, self.adjust_preview
                    )
                    source_item = SourceListWidgetItem(self)
                    source_item.setSizeHint(source_widget.sizeHint())
                    self.insertItem(0, source_item)
                    self.setItemWidget(source_item, source_widget)
                    self.source_items[source_uuid] = source_item
                except sqlalchemy.exc.InvalidRequestError as e:
                    logger.debug(e)

            # Re-sort SourceList to make sure the most recently-updated sources appear at the top
            self.sortItems(Qt.DescendingOrder)

            # ATTENTION! 32 is an arbitrary number arrived at via
            # experimentation. It adds plenty of sources, but doesn't block
            # for a noticable amount of time.
            new_slice_size = min(self.NUM_SOURCES_TO_ADD_AT_A_TIME, slice_size * 2)
            # Call add_source again for the remaining sources.
            self.add_source(sources[slice_size:], new_slice_size)

        # Schedule the closure defined above in the next iteration of the
        # Qt event loop (thus unblocking the UI).
        QTimer.singleShot(1, schedule_source_management)

    def get_selected_source(self) -> Optional[Source]:
        if not self.selectedItems():
            return None

        source_item = self.selectedItems()[0]
        source_widget = self.itemWidget(source_item)
        if source_widget and source_exists(self.controller.session, source_widget.source_uuid):
            return source_widget.source
        return None  # pragma: nocover

    def get_source_widget(self, source_uuid: str) -> Optional[QListWidget]:
        """
        First try to get the source widget from the cache, then look for it in the SourceList.
        """
        try:
            source_item = self.source_items[source_uuid]
            return self.itemWidget(source_item)
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
        """
        Set the source widget's preview snippet with the supplied content.

        Note: The signal's `collection_item_uuid` is not needed for setting the preview snippet. It
        is used by other signal handlers.
        """
        source_widget = self.get_source_widget(source_uuid)
        if source_widget:
            source_widget.set_snippet(source_uuid, collection_item_uuid, content)


class SourcePreview(SecureQLabel):
    PREVIEW_WIDTH_DIFFERENCE = 140

    def __init__(self) -> None:
        super().__init__()

    def adjust_preview(self, width: int) -> None:
        """
        This is a workaround to the workaround for https://bugreports.qt.io/browse/QTBUG-85498.
        Since QLabels containing text with long strings that cannot be wrapped have to have a fixed
        width in order to fit within the scroll list widget, we have to override the normal resizing
        logic.
        """
        new_width = width - self.PREVIEW_WIDTH_DIFFERENCE
        if self.width() == new_width:
            return

        self.setFixedWidth(new_width)
        self.max_length = self.width()
        self.refresh_preview_text()


class ConversationDeletionIndicator(QWidget):
    """
    Shown when a source's conversation content is being deleted.
    """

    def __init__(self) -> None:
        super().__init__()

        self.hide()

        self.setObjectName("ConversationDeletionIndicator")

        palette = QPalette()
        palette.setBrush(QPalette.Background, QBrush(QColor("#9495b9")))
        palette.setBrush(QPalette.Foreground, QBrush(QColor("#ffffff")))
        self.setPalette(palette)
        self.setAutoFillBackground(True)

        deletion_message = QLabel(_("Deleting files and messages..."))
        deletion_message.setWordWrap(False)

        self.animation = load_movie("loading-cubes.gif")
        self.animation.setScaledSize(QSize(50, 50))

        spinner = QLabel()
        spinner.setMovie(self.animation)

        layout = QGridLayout()
        layout.setContentsMargins(20, 20, 20, 20)
        layout.setSpacing(0)
        layout.addWidget(deletion_message, 0, 0, Qt.AlignRight | Qt.AlignVCenter)
        layout.addWidget(spinner, 0, 1, Qt.AlignLeft | Qt.AlignVCenter)
        layout.setColumnStretch(0, 9)
        layout.setColumnStretch(1, 7)

        self.setLayout(layout)

    def start(self) -> None:
        self.animation.start()
        self.show()

    def stop(self) -> None:
        self.animation.stop()
        self.hide()


class SourceDeletionIndicator(QWidget):
    """
    Shown when a source is being deleted.
    """

    def __init__(self) -> None:
        super().__init__()

        self.hide()

        self.setObjectName("SourceDeletionIndicator")

        palette = QPalette()
        palette.setBrush(QPalette.Background, QBrush(QColor("#9495b9")))
        palette.setBrush(QPalette.Foreground, QBrush(QColor("#ffffff")))
        self.setPalette(palette)
        self.setAutoFillBackground(True)

        self.deletion_message = QLabel(_("Deleting source account..."))
        self.deletion_message.setWordWrap(False)

        self.animation = load_movie("loading-cubes.gif")
        self.animation.setScaledSize(QSize(50, 50))

        spinner = QLabel()
        spinner.setMovie(self.animation)

        layout = QGridLayout()
        layout.setContentsMargins(20, 20, 20, 20)
        layout.setSpacing(0)

        layout.addWidget(self.deletion_message, 0, 0, Qt.AlignRight | Qt.AlignVCenter)
        layout.addWidget(spinner, 0, 1, Qt.AlignLeft | Qt.AlignVCenter)
        layout.setColumnStretch(0, 9)
        layout.setColumnStretch(1, 7)

        self.setLayout(layout)

    def start(self) -> None:
        self.animation.start()
        self.show()

    def stop(self) -> None:
        self.animation.stop()
        self.hide()


class SourceWidgetDeletionIndicator(QLabel):
    """
    Shown in the source list when a source's conversation content is being deleted.
    """

    def __init__(self) -> None:
        super().__init__()

        self.hide()

        self.setObjectName("SourceWidgetDeletionIndicator")

        self.animation = load_movie("loading-bar.gif")
        self.animation.setScaledSize(QSize(200, 11))

        self.setMovie(self.animation)

    def start(self) -> None:
        self.animation.start()
        self.show()

    def stop(self) -> None:
        self.animation.stop()
        self.hide()


class SourceWidget(QWidget):
    """
    Used to display summary information about a source in the list view.
    """

    TOP_MARGIN = 11
    BOTTOM_MARGIN = 7
    SIDE_MARGIN = 10
    SPACER = 14
    BOTTOM_SPACER = 11
    STAR_WIDTH = 20
    TIMESTAMP_WIDTH = 60

    SOURCE_NAME_CSS = load_css("source_name.css")
    SOURCE_PREVIEW_CSS = load_css("source_preview.css")
    SOURCE_TIMESTAMP_CSS = load_css("source_timestamp.css")

    deleting = False

    def __init__(
        self,
        controller: Controller,
        source: Source,
        source_selected_signal: pyqtSignal,
        adjust_preview: pyqtSignal,
    ):
        super().__init__()

        self.controller = controller
        self.controller.conversation_deleted.connect(self._on_conversation_deleted)
        self.controller.conversation_deletion_failed.connect(self._on_conversation_deletion_failed)
        self.controller.source_deleted.connect(self._on_source_deleted)
        self.controller.source_deletion_failed.connect(self._on_source_deletion_failed)
        self.controller.authentication_state.connect(self._on_authentication_changed)
        source_selected_signal.connect(self._on_source_selected)
        adjust_preview.connect(self._on_adjust_preview)

        self.source = source
        self.seen = self.source.seen
        self.source_uuid = self.source.uuid
        self.last_updated = self.source.last_updated
        self.selected = False

        self.setCursor(QCursor(Qt.PointingHandCursor))

        retain_space = self.sizePolicy()
        retain_space.setRetainSizeWhenHidden(True)
        self.star = StarToggleButton(self.controller, self.source_uuid, source.is_starred)
        self.star.setSizePolicy(retain_space)
        self.star.setFixedWidth(self.STAR_WIDTH)
        self.name = QLabel()
        self.name.setObjectName("SourceWidget_name")
        self.preview = SourcePreview()
        self.preview.setObjectName("SourceWidget_preview")
        self.deletion_indicator = SourceWidgetDeletionIndicator()

        self.paperclip = SvgLabel("paperclip.svg", QSize(11, 17))  # Set to size provided in the svg
        self.paperclip.setObjectName("SourceWidget_paperclip")
        self.paperclip.setFixedSize(QSize(11, 17))
        self.paperclip.setSizePolicy(retain_space)

        self.paperclip_disabled = SvgLabel("paperclip-disabled.svg", QSize(11, 17))
        self.paperclip_disabled.setObjectName("SourceWidget_paperclip")
        self.paperclip_disabled.setFixedSize(QSize(11, 17))
        self.paperclip_disabled.setSizePolicy(retain_space)
        self.paperclip_disabled.hide()

        self.timestamp = QLabel()
        self.timestamp.setSizePolicy(retain_space)
        self.timestamp.setFixedWidth(self.TIMESTAMP_WIDTH)
        self.timestamp.setObjectName("SourceWidget_timestamp")

        # Create source_widget:
        # -------------------------------------------------------------------
        # | ------ | -------- | ------                   | -----------      |
        # | |star| | |spacer| | |name|                   | |paperclip|      |
        # | ------ | -------- | ------                   | -----------      |
        # -------------------------------------------------------------------
        # |        |          | ---------                | -----------      |
        # |        |          | |preview|                | |timestamp|      |
        # |        |          | ---------                | -----------      |
        # ------------------------------------------- -----------------------
        # Column 0, 1, and 3 are fixed. Column 2 stretches.
        self.source_widget = QWidget()
        self.source_widget.setObjectName("SourceWidget_container")
        source_widget_layout = QGridLayout()
        source_widget_layout.setSpacing(0)
        source_widget_layout.setContentsMargins(0, self.TOP_MARGIN, 0, self.BOTTOM_MARGIN)
        source_widget_layout.addWidget(self.star, 0, 0, 1, 1)
        self.spacer = QWidget()
        self.spacer.setFixedWidth(self.SPACER)
        source_widget_layout.addWidget(self.spacer, 0, 1, 1, 1)
        source_widget_layout.addWidget(self.name, 0, 2, 1, 1)
        source_widget_layout.addWidget(self.paperclip, 0, 3, 1, 1)
        source_widget_layout.addWidget(self.paperclip_disabled, 0, 3, 1, 1)
        source_widget_layout.addWidget(self.preview, 1, 2, 1, 1, alignment=Qt.AlignLeft)
        source_widget_layout.addWidget(self.deletion_indicator, 1, 2, 1, 1)
        source_widget_layout.addWidget(self.timestamp, 1, 3, 1, 1)
        source_widget_layout.addItem(QSpacerItem(self.BOTTOM_SPACER, self.BOTTOM_SPACER))
        self.source_widget.setLayout(source_widget_layout)
        layout = QHBoxLayout(self)
        self.setLayout(layout)
        layout.setContentsMargins(self.SIDE_MARGIN, 0, self.SIDE_MARGIN, 0)
        layout.setSpacing(0)
        layout.addWidget(self.source_widget)

        self.update()

    @pyqtSlot(int)
    def _on_adjust_preview(self, width: int) -> None:
        self.setFixedWidth(width)
        self.preview.adjust_preview(width)

    def update(self) -> None:
        """
        Updates the displayed values with the current values from self.source.
        """
        try:
            self.controller.session.refresh(self.source)
            self.last_updated = self.source.last_updated
            self.timestamp.setText(_(arrow.get(self.source.last_updated).format("MMM D")))
            self.name.setText(self.source.journalist_designation)

            self.set_snippet(self.source_uuid)

            if self.source.document_count == 0:
                self.paperclip.hide()
                self.paperclip_disabled.hide()

            if not self.source.server_collection and self.source.interaction_count > 0:
                self.preview.setProperty("class", "conversation_deleted")
            else:
                self.preview.setProperty("class", "")

            self.star.update(self.source.is_starred)

            self.end_deletion()

            # When not authenticated we always show the source as having been seen
            self.seen = True if not self.controller.is_authenticated else self.source.seen
            self.update_styles()
        except sqlalchemy.exc.InvalidRequestError as e:
            logger.debug(f"Could not update SourceWidget for source {self.source_uuid}: {e}")

    @pyqtSlot(str, str, str)
    def set_snippet(
        self, source_uuid: str, collection_uuid: str = None, content: str = None
    ) -> None:
        """
        Update the preview snippet if the source_uuid matches our own.
        """
        if source_uuid != self.source_uuid:
            return

        if self.deleting:
            content = ""
        elif not self.source.server_collection:
            if self.source.interaction_count > 0:
                # The server only ever increases the interaction
                # count, so if it's non-zero but the source collection
                # is empty, we know the conversation has been deleted.
                content = _("\u2014 All files and messages deleted for this source \u2014")
            else:
                content = ""
        else:
            last_activity = self.source.server_collection[-1]
            if collection_uuid and collection_uuid != last_activity.uuid:
                return

            if not content:
                content = str(last_activity)

        self.preview.setText(content)
        self.preview.adjust_preview(self.width())

    def update_styles(self) -> None:
        if self.seen:
            self.name.setStyleSheet("")
            if self.selected:
                self.name.setObjectName("SourceWidget_name_selected")
            else:
                self.name.setObjectName("SourceWidget_name")
            self.name.setStyleSheet(self.SOURCE_NAME_CSS)

            self.timestamp.setStyleSheet("")
            self.timestamp.setObjectName("SourceWidget_timestamp")
            self.timestamp.setStyleSheet(self.SOURCE_TIMESTAMP_CSS)

            self.preview.setStyleSheet("")
            self.preview.setObjectName("SourceWidget_preview")
            self.preview.setStyleSheet(self.SOURCE_PREVIEW_CSS)
        else:
            self.name.setStyleSheet("")
            self.name.setObjectName("SourceWidget_name_unread")
            self.name.setStyleSheet(self.SOURCE_NAME_CSS)

            self.timestamp.setStyleSheet("")
            self.timestamp.setObjectName("SourceWidget_timestamp_unread")
            self.timestamp.setStyleSheet(self.SOURCE_TIMESTAMP_CSS)

            self.preview.setStyleSheet("")
            self.preview.setObjectName("SourceWidget_preview_unread")
            self.preview.setStyleSheet(self.SOURCE_PREVIEW_CSS)

    @pyqtSlot(bool)
    def _on_authentication_changed(self, authenticated: bool) -> None:
        """
        When the user logs out, show source as seen.
        """
        if not authenticated:
            self.seen = True
            self.update_styles()

    @pyqtSlot(str)
    def _on_source_selected(self, selected_source_uuid: str) -> None:
        """
        Show selected widget as having been seen.
        """
        if self.source_uuid == selected_source_uuid:
            self.seen = True
            self.selected = True
            self.update_styles()
        else:
            self.selected = False
            self.update_styles()

    @pyqtSlot(str)
    def _on_conversation_deleted(self, source_uuid: str) -> None:
        if self.source_uuid == source_uuid:
            self.start_conversation_deletion()

    @pyqtSlot(str)
    def _on_conversation_deletion_failed(self, source_uuid: str) -> None:
        if self.source_uuid == source_uuid:
            self.end_conversation_deletion()

    @pyqtSlot(str)
    def _on_source_deleted(self, source_uuid: str) -> None:
        if self.source_uuid == source_uuid:
            self.start_account_deletion()

    @pyqtSlot(str)
    def _on_source_deletion_failed(self, source_uuid: str) -> None:
        if self.source_uuid == source_uuid:
            self.end_account_deletion()

    def end_account_deletion(self) -> None:
        self.end_deletion()
        self.star.show()
        self.name.setProperty("class", "")
        self.timestamp.setProperty("class", "")
        self.update_styles()
        self.deleting = False

    def end_conversation_deletion(self) -> None:
        self.end_deletion()
        self.deleting_conversation = False

    def end_deletion(self) -> None:
        self.deletion_indicator.stop()
        self.preview.show()
        self.timestamp.show()
        self.paperclip_disabled.hide()
        if self.source.document_count != 0:
            self.paperclip.show()

    def start_account_deletion(self) -> None:
        self.deleting = True
        self.start_deletion()
        self.name.setProperty("class", "deleting")
        self.timestamp.setProperty("class", "deleting")
        self.star.hide()
        self.update_styles()

    def start_conversation_deletion(self) -> None:
        self.deleting_conversation = True
        self.start_deletion()

    def start_deletion(self) -> None:
        self.preview.hide()
        self.paperclip.hide()
        if self.source.document_count != 0:
            self.paperclip_disabled.show()
        self.deletion_indicator.start()


class StarToggleButton(SvgToggleButton):
    """
    A button that shows whether or not a source is starred
    """

    def __init__(self, controller: Controller, source_uuid: str, is_starred: bool) -> None:
        super().__init__(on="star_on.svg", off="star_off.svg", svg_size=QSize(16, 16))

        self.controller = controller
        self.source_uuid = source_uuid
        self.is_starred = is_starred
        self.pending_count = 0
        self.wait_until_next_sync = False

        self.controller.authentication_state.connect(self.on_authentication_changed)
        self.controller.star_update_failed.connect(self.on_star_update_failed)
        self.controller.star_update_successful.connect(self.on_star_update_successful)
        self.installEventFilter(self)

        self.setObjectName("StarToggleButton")
        self.setFixedSize(QSize(20, 20))

        self.pressed.connect(self.on_pressed)
        self.setCheckable(True)
        self.setChecked(self.is_starred)

        if not self.controller.is_authenticated:
            self.disable_toggle()

    def disable_toggle(self) -> None:
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
            self.set_icon(on="star_on.svg", off="star_on.svg")
        self.setCheckable(False)

    def enable_toggle(self) -> None:
        """
        Enable the widget.

        Disconnect the pressed signal from previous handler, set checkable so that the star can be
        toggled, and connect to the online toggle handler.

        Note: We must update the icon in case it was modified after being disabled.
        """
        self.pressed.disconnect()
        self.pressed.connect(self.on_pressed)
        self.setCheckable(True)
        self.set_icon(on="star_on.svg", off="star_off.svg")  # Undo icon change from disable_toggle

    def eventFilter(self, obj: QObject, event: QEvent) -> None:
        """
        If the button is checkable then we show a hover state.
        """
        if not self.isCheckable():
            return QObject.event(obj, event)

        t = event.type()
        if t == QEvent.HoverEnter:
            self.setIcon(load_icon("star_hover.svg"))
        elif t == QEvent.HoverLeave or t == QEvent.MouseButtonPress:
            self.set_icon(on="star_on.svg", off="star_off.svg")

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


class LoginOfflineLink(SDPushButton):
    """A button that logs the user in, in offline mode."""

    def __init__(self, parent: QWidget = None) -> None:
        super().__init__(parent)
        self.setText(_("USE OFFLINE"))
        self.setAlignment(SDPushButton.AlignLeft)


class SignInButton(QPushButton):
    """
    A button that logs the user into application when clicked.
    """

    def __init__(self, parent: QWidget = None) -> None:
        super().__init__(parent)
        self.setText(_("SIGN IN"))

        # Set css id
        self.setObjectName("SignInButton")

        self.setFixedHeight(40)
        self.setFixedWidth(140)

        # Set cursor.
        self.setCursor(QCursor(Qt.PointingHandCursor))

        # Set drop shadow effect
        effect = QGraphicsDropShadowEffect(self)
        effect.setOffset(0, 1)
        effect.setBlurRadius(8)
        effect.setColor(QColor("#aa000000"))
        self.setGraphicsEffect(effect)
        self.update()


class LoginErrorBar(QWidget):
    """
    A bar widget for displaying messages about login errors to the user.
    """

    def __init__(self) -> None:
        super().__init__()

        self.setObjectName("LoginErrorBar")

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
        self.error_icon = SvgLabel("error_icon_white.svg", svg_size=QSize(18, 18))
        self.error_icon.setObjectName("LoginErrorBar_icon")
        self.error_icon.setFixedWidth(42)

        # Error status bar
        self.error_status_bar = SecureQLabel(wordwrap=False)
        self.error_status_bar.setObjectName("LoginErrorBar_status_bar")
        self.setFixedHeight(42)

        # Create space ths size of the error icon to keep the error message centered
        spacer1 = QWidget()
        spacer2 = QWidget()

        # Add widgets to layout
        layout.addWidget(spacer1)
        layout.addWidget(self.error_icon)
        layout.addWidget(self.error_status_bar)
        layout.addWidget(spacer2)

    def set_message(self, message: str) -> None:
        self.show()
        self.error_status_bar.setText(message)

    def clear_message(self) -> None:
        self.error_status_bar.setText("")
        self.hide()


class PasswordEdit(QLineEdit):
    """
    A LineEdit with icons to show/hide password entries
    """

    def __init__(self, parent: QDialog) -> None:
        self.parent = parent
        super().__init__(self.parent)

        self.visibleIcon = load_icon("eye_visible.svg")
        self.hiddenIcon = load_icon("eye_hidden.svg")

        self.setEchoMode(QLineEdit.Password)
        self.togglepasswordAction = self.addAction(self.hiddenIcon, QLineEdit.TrailingPosition)
        self.togglepasswordAction.triggered.connect(self.on_toggle_password_Action)
        self.password_shown = False

    def on_toggle_password_Action(self) -> None:
        if not self.password_shown:
            self.setEchoMode(QLineEdit.Normal)
            self.password_shown = True
            self.togglepasswordAction.setIcon(self.visibleIcon)
        else:
            self.setEchoMode(QLineEdit.Password)
            self.password_shown = False
            self.togglepasswordAction.setIcon(self.hiddenIcon)


class SenderIcon(QWidget):
    """
    Represents a reply to a source.
    """

    SENDER_ICON_CSS = load_css("sender_icon.css")

    def __init__(self) -> None:
        super().__init__()
        self._is_current_user = False
        self._initials = ""
        self.setObjectName("SenderIcon")
        self.setStyleSheet(self.SENDER_ICON_CSS)
        self.setFixedSize(QSize(48, 48))
        font = QFont()
        font.setLetterSpacing(QFont.AbsoluteSpacing, 0.58)
        self.label = QLabel()
        self.label.setAlignment(Qt.AlignCenter)
        self.label.setFont(font)
        layout = QVBoxLayout()
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)
        layout.addWidget(self.label)
        self.setLayout(layout)

    @property
    def is_current_user(self) -> bool:
        return self._is_current_user

    @is_current_user.setter
    def is_current_user(self, is_current_user: bool) -> None:
        if self._is_current_user != is_current_user:
            self._is_current_user = is_current_user

    @property
    def initials(self) -> str:
        return self._initials

    @initials.setter
    def initials(self, initials: str) -> None:
        if not initials:
            self.label.setPixmap(load_image("deleted-user.svg"))
        else:
            self.label.setText(initials)

        if self._initials != initials:
            self._initials = initials

    def set_normal_styles(self) -> None:
        self.setStyleSheet("")
        if self.is_current_user:
            self.setObjectName("SenderIcon_current_user")
        else:
            self.setObjectName("SenderIcon")
        self.setStyleSheet(self.SENDER_ICON_CSS)

    def set_failed_styles(self) -> None:
        self.setStyleSheet("")
        self.setObjectName("SenderIcon_failed")
        self.setStyleSheet(self.SENDER_ICON_CSS)

    def set_pending_styles(self) -> None:
        self.setStyleSheet("")
        if self.is_current_user:
            self.setObjectName("SenderIcon_current_user_pending")
        else:
            self.setObjectName("SenderIcon_pending")
        self.setStyleSheet(self.SENDER_ICON_CSS)

    def set_failed_to_decrypt_styles(self) -> None:
        self.setStyleSheet("")
        self.setObjectName("SenderIcon_failed_to_decrypt")
        self.setStyleSheet(self.SENDER_ICON_CSS)


class SpeechBubble(QWidget):
    """
    Represents a speech bubble that's part of a conversation between a source
    and journalist.
    """

    MESSAGE_CSS = load_css("speech_bubble_message.css")
    STATUS_BAR_CSS = load_css("speech_bubble_status_bar.css")

    WIDTH_TO_CONTAINER_WIDTH_RATIO = 5 / 9
    MIN_WIDTH = 400
    MIN_CONTAINER_WIDTH = 750

    TOP_MARGIN = 28
    BOTTOM_MARGIN = 0

    def __init__(  # type: ignore [no-untyped-def]
        self,
        message_uuid: str,
        text: str,
        update_signal,
        download_error_signal,
        index: int,
        container_width: int,
        failed_to_decrypt: bool = False,
    ) -> None:
        super().__init__()

        self.uuid = message_uuid
        self.index = index
        self.failed_to_decrypt = failed_to_decrypt

        # Set layout
        layout = QVBoxLayout()
        self.setLayout(layout)

        # Set margins and spacing
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Message box
        self.message = SecureQLabel(text)
        self.message.setObjectName("SpeechBubble_message")
        self.message.setStyleSheet(self.MESSAGE_CSS)

        # Color bar
        self.color_bar = QWidget()
        self.color_bar.setObjectName("SpeechBubble_status_bar")
        self.color_bar.setStyleSheet(self.STATUS_BAR_CSS)

        # User icon
        self.sender_icon = SenderIcon()
        self.sender_icon.hide()

        # Speech bubble
        self.speech_bubble = QWidget()
        speech_bubble_layout = QVBoxLayout()
        self.speech_bubble.setLayout(speech_bubble_layout)
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
        self.bubble_area_layout.addWidget(self.sender_icon, alignment=Qt.AlignBottom)
        self.bubble_area_layout.addWidget(self.speech_bubble)

        # Add widget to layout
        layout.addWidget(bubble_area)

        # Make text selectable but disable the context menu
        self.message.setTextInteractionFlags(Qt.TextSelectableByMouse)
        self.message.setContextMenuPolicy(Qt.NoContextMenu)

        if self.failed_to_decrypt:
            self.set_failed_to_decrypt_styles()

        # Connect signals to slots
        update_signal.connect(self._update_text)
        download_error_signal.connect(self._on_download_error)

        self.adjust_width(container_width)

    def adjust_width(self, container_width: int) -> None:
        """
        This is a workaround to the workaround for https://bugreports.qt.io/browse/QTBUG-85498.
        Since QLabels containing text with long strings that cannot be wrapped have to have a fixed
        width in order to fit within the scrollarea widget, we have to override the normal resizing
        logic.
        """
        if container_width < self.MIN_CONTAINER_WIDTH:
            self.speech_bubble.setFixedWidth(self.MIN_WIDTH)
        else:
            self.speech_bubble.setFixedWidth(container_width * self.WIDTH_TO_CONTAINER_WIDTH_RATIO)

    @pyqtSlot(str, str, str)
    def _update_text(self, source_uuid: str, uuid: str, text: str) -> None:
        """
        Conditionally update this SpeechBubble's text if and only if the message_uuid of the emitted
        signal matches the uuid of this speech bubble.
        """
        if self.uuid == uuid:
            self.message.setText(text)
            self.set_normal_styles()

    @pyqtSlot(str, str, str)
    def _on_download_error(self, source_uuid: str, uuid: str, text: str) -> None:
        """
        Adjust style and text to indicate an error.
        """
        if self.uuid == uuid:
            self.message.setText(text)
            self.failed_to_decrypt = True
            self.set_failed_to_decrypt_styles()

    def set_normal_styles(self) -> None:
        self.message.setStyleSheet("")
        self.message.setObjectName("SpeechBubble_message")
        self.message.setStyleSheet(self.MESSAGE_CSS)
        self.color_bar.setStyleSheet("")
        self.color_bar.setObjectName("SpeechBubble_status_bar")
        self.color_bar.setStyleSheet(self.STATUS_BAR_CSS)

    def set_failed_to_decrypt_styles(self) -> None:
        self.message.setStyleSheet("")
        self.message.setObjectName("SpeechBubble_message_decryption_error")
        self.message.setStyleSheet(self.MESSAGE_CSS)
        self.color_bar.setStyleSheet("")
        self.color_bar.setObjectName("SpeechBubble_status_bar_decryption_error")
        self.color_bar.setStyleSheet(self.STATUS_BAR_CSS)
        self.sender_icon.set_failed_to_decrypt_styles()


class MessageWidget(SpeechBubble):
    """
    Represents an incoming message from the source.
    """

    def __init__(  # type: ignore [no-untyped-def]
        self,
        message_uuid: str,
        message: str,
        update_signal,
        download_error_signal,
        index: int,
        container_width: int,
        failed_to_decrypt: bool = False,
    ) -> None:
        super().__init__(
            message_uuid,
            message,
            update_signal,
            download_error_signal,
            index,
            container_width,
            failed_to_decrypt,
        )


class ReplyWidget(SpeechBubble):
    """
    Represents a reply to a source.
    """

    MESSAGE_CSS = load_css("speech_bubble_message.css")
    STATUS_BAR_CSS = load_css("speech_bubble_status_bar.css")

    ERROR_BOTTOM_MARGIN = 20

    def __init__(  # type: ignore [no-untyped-def]
        self,
        controller: Controller,
        message_uuid: str,
        message: str,
        reply_status: str,
        update_signal,
        download_error_signal,
        message_succeeded_signal,
        message_failed_signal,
        index: int,
        container_width: int,
        sender: User,
        sender_is_current_user: bool,
        failed_to_decrypt: bool = False,
    ) -> None:
        super().__init__(
            message_uuid,
            message,
            update_signal,
            download_error_signal,
            index,
            container_width,
            failed_to_decrypt,
        )
        self.controller = controller
        self.status = reply_status
        self.uuid = message_uuid
        self._sender = sender
        self._sender_is_current_user = sender_is_current_user
        self.failed_to_decrypt = failed_to_decrypt

        self.error = QWidget()
        error_layout = QHBoxLayout()
        error_layout.setContentsMargins(0, 0, 0, self.ERROR_BOTTOM_MARGIN)
        error_layout.setSpacing(4)
        self.error.setLayout(error_layout)
        error_message = SecureQLabel(_("Failed to send"), wordwrap=False)
        error_message.setObjectName("ReplyWidget_failed_to_send_text")
        error_icon = SvgLabel("error_icon.svg", svg_size=QSize(12, 12))
        error_icon.setFixedWidth(12)
        error_layout.addWidget(error_message)
        error_layout.addWidget(error_icon)
        retain_space = self.sizePolicy()
        retain_space.setRetainSizeWhenHidden(True)
        self.error.setSizePolicy(retain_space)
        self.error.hide()

        self.bubble_area_layout.addWidget(self.error, alignment=Qt.AlignBottom)
        self.sender_icon.show()

        message_succeeded_signal.connect(self._on_reply_success)
        message_failed_signal.connect(self._on_reply_failure)
        self.controller.update_authenticated_user.connect(self._on_update_authenticated_user)
        self.controller.authentication_state.connect(self._on_authentication_changed)

        self.sender_icon.is_current_user = self._sender_is_current_user
        if self._sender:
            self.sender_icon.initials = self._sender.initials
            self.sender_icon.setToolTip(self._sender.fullname)
        self._update_styles()

    @property
    def sender_is_current_user(self) -> bool:
        return self._sender_is_current_user

    @sender_is_current_user.setter
    def sender_is_current_user(self, sender_is_current_user: bool) -> None:
        if self._sender_is_current_user != sender_is_current_user:
            self._sender_is_current_user = sender_is_current_user
            self.sender_icon.is_current_user = sender_is_current_user

    @property
    def sender(self) -> User:
        return self._sender

    @sender.setter
    def sender(self, sender: User) -> None:
        if self._sender != sender:
            self._sender = sender

        if self._sender:
            self.sender_icon.initials = self._sender.initials
            self.sender_icon.setToolTip(self._sender.fullname)

    @pyqtSlot(bool)
    def _on_authentication_changed(self, authenticated: bool) -> None:
        """
        When the user logs out, update the reply badge.
        """
        if not authenticated:
            self.sender_is_current_user = False
            self._update_styles()

    @pyqtSlot(User)
    def _on_update_authenticated_user(self, user: User) -> None:
        """
        When the user logs in or updates user info, update the reply badge.
        """
        if user.uuid == self.sender.uuid:
            self.sender_is_current_user = True
            self.sender = user
            self.sender_icon.setToolTip(self.sender.fullname)
            self._update_styles()

    @pyqtSlot(str, str, str)
    def _on_reply_success(self, source_uuid: str, uuid: str, content: str) -> None:
        """
        Conditionally update this ReplyWidget's state if and only if the message_uuid of the emitted
        signal matches the uuid of this widget.
        """
        if self.uuid == uuid:
            self.status = "SUCCEEDED"  # TODO: Add and use success status in db.ReplySendStatusCodes
            self.failed_to_decrypt = False
            self._update_styles()

    @pyqtSlot(str)
    def _on_reply_failure(self, uuid: str) -> None:
        """
        Conditionally update this ReplyWidget's state if and only if the message_uuid of the emitted
        signal matches the uuid of this widget.
        """
        if self.uuid == uuid:
            self.status = ReplySendStatusCodes.FAILED.value
            self.failed_to_decrypt = False
            self._update_styles()

    def _update_styles(self) -> None:
        if self.failed_to_decrypt:
            self.set_failed_to_decrypt_styles()
        elif self.status == ReplySendStatusCodes.PENDING.value:
            self.set_pending_styles()
        elif self.status == ReplySendStatusCodes.FAILED.value:
            self.set_failed_styles()
            self.error.show()
        else:
            self.set_normal_styles()
            self.error.hide()

    def set_normal_styles(self) -> None:
        self.message.setStyleSheet("")
        self.message.setObjectName("SpeechBubble_reply")
        self.message.setStyleSheet(self.MESSAGE_CSS)

        self.sender_icon.set_normal_styles()

        self.color_bar.setStyleSheet("")
        if self.sender_is_current_user:
            self.color_bar.setObjectName("ReplyWidget_status_bar_current_user")
        else:
            self.color_bar.setObjectName("ReplyWidget_status_bar")
        self.color_bar.setStyleSheet(self.STATUS_BAR_CSS)

    def set_pending_styles(self) -> None:
        self.message.setStyleSheet("")
        self.message.setObjectName("ReplyWidget_message_pending")
        self.message.setStyleSheet(self.MESSAGE_CSS)

        self.sender_icon.set_pending_styles()

        self.color_bar.setStyleSheet("")
        if self.sender_is_current_user:
            self.color_bar.setObjectName("ReplyWidget_status_bar_pending_current_user")
        else:
            self.color_bar.setObjectName("ReplyWidget_status_bar_pending")
        self.color_bar.setStyleSheet(self.STATUS_BAR_CSS)

    def set_failed_styles(self) -> None:
        self.message.setStyleSheet("")
        self.message.setObjectName("ReplyWidget_message_failed")
        self.message.setStyleSheet(self.MESSAGE_CSS)
        self.sender_icon.set_failed_styles()
        self.color_bar.setStyleSheet("")
        self.color_bar.setObjectName("ReplyWidget_status_bar_failed")
        self.color_bar.setStyleSheet(self.STATUS_BAR_CSS)


class FileWidget(QWidget):
    """
    Represents a file.
    """

    DOWNLOAD_BUTTON_CSS = load_css("file_download_button.css")

    TOP_MARGIN = 18
    BOTTOM_MARGIN = 0
    FILE_FONT_SPACING = 2
    FILE_OPTIONS_FONT_SPACING = 1.6
    FILENAME_WIDTH_PX = 360
    FILE_OPTIONS_LAYOUT_SPACING = 8

    WIDTH_TO_CONTAINER_WIDTH_RATIO = 5 / 9
    MIN_CONTAINER_WIDTH = 750
    MIN_WIDTH = 400

    def __init__(
        self,
        file_uuid: str,
        controller: Controller,
        file_ready_signal: pyqtBoundSignal,
        file_missing: pyqtBoundSignal,
        index: int,
        container_width: int,
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

        self.adjust_width(container_width)

        self.setObjectName("FileWidget")
        file_description_font = QFont()
        file_description_font.setLetterSpacing(QFont.AbsoluteSpacing, self.FILE_FONT_SPACING)
        self.file_buttons_font = QFont()
        self.file_buttons_font.setLetterSpacing(
            QFont.AbsoluteSpacing, self.FILE_OPTIONS_FONT_SPACING
        )

        # Set layout
        layout = QHBoxLayout()
        self.setLayout(layout)

        # Set margins and spacing
        layout.setContentsMargins(0, self.TOP_MARGIN, 0, self.BOTTOM_MARGIN)
        layout.setSpacing(0)

        # File options: download, export, print
        self.file_options = QWidget()
        self.file_options.setObjectName("FileWidget_file_options")
        file_options_layout = QHBoxLayout()
        self.file_options.setLayout(file_options_layout)
        file_options_layout.setContentsMargins(0, 0, 0, 0)
        file_options_layout.setSpacing(self.FILE_OPTIONS_LAYOUT_SPACING)
        file_options_layout.setAlignment(Qt.AlignLeft)
        self.download_button = QPushButton(_(" DOWNLOAD"))
        self.download_button.setObjectName("FileWidget_download_button")
        self.download_button.setStyleSheet(self.DOWNLOAD_BUTTON_CSS)
        self.download_button.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)
        self.download_button.setIcon(load_icon("download_file.svg"))
        self.download_button.setFont(self.file_buttons_font)
        self.download_button.setCursor(QCursor(Qt.PointingHandCursor))
        self.download_animation = load_movie("download_file.gif")
        self.export_button = QPushButton(_("EXPORT"))
        self.export_button.setObjectName("FileWidget_export_print")
        self.export_button.setFont(self.file_buttons_font)
        self.export_button.setCursor(QCursor(Qt.PointingHandCursor))
        self.middot = QLabel("·")  # nosemgrep: semgrep.untranslated-gui-string
        self.print_button = QPushButton(_("PRINT"))
        self.print_button.setObjectName("FileWidget_export_print")
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
        self.file_name.setObjectName("FileWidget_file_name")
        self.file_name.installEventFilter(self)
        self.file_name.setCursor(QCursor(Qt.PointingHandCursor))
        self.no_file_name = SecureQLabel(_("ENCRYPTED FILE ON SERVER"), wordwrap=False)
        self.no_file_name.setObjectName("FileWidget_no_file_name")
        self.no_file_name.setFont(file_description_font)

        # Line between file name and file size
        self.horizontal_line = QWidget()
        self.horizontal_line.setObjectName("FileWidget_horizontal_line")
        self.horizontal_line.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        # Space between elided file name and file size when horizontal line is hidden
        self.spacer = QWidget()
        self.spacer.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        self.spacer.hide()

        # File size
        self.file_size = SecureQLabel(humanize_filesize(self.file.size))
        self.file_size.setObjectName("FileWidget_file_size")
        self.file_size.setAlignment(Qt.AlignRight)

        # Decide what to show or hide based on whether or not the file's been downloaded
        self._set_file_state()

        # Add widgets
        layout.addWidget(self.file_options)
        layout.addWidget(self.file_name)
        layout.addWidget(self.no_file_name)
        layout.addWidget(self.spacer)
        layout.addWidget(self.horizontal_line)
        layout.addWidget(self.file_size)

        # Connect signals to slots
        file_ready_signal.connect(self._on_file_downloaded, type=Qt.QueuedConnection)
        file_missing.connect(self._on_file_missing, type=Qt.QueuedConnection)

    def adjust_width(self, container_width: int) -> None:
        """
        This is a workaround to the workaround for https://bugreports.qt.io/browse/QTBUG-85498.
        See comment in the adjust_width method for SpeechBubble.
        """
        if container_width < self.MIN_CONTAINER_WIDTH:
            self.setFixedWidth(self.MIN_WIDTH)
        else:
            self.setFixedWidth(container_width * self.WIDTH_TO_CONTAINER_WIDTH_RATIO)

    def eventFilter(self, obj: QObject, event: QEvent) -> None:
        t = event.type()
        if t == QEvent.MouseButtonPress:
            if event.button() == Qt.LeftButton:
                self._on_left_click()
        elif t == QEvent.HoverEnter and not self.downloading:
            self.download_button.setIcon(load_icon("download_file_hover.svg"))
        elif t == QEvent.HoverLeave and not self.downloading:
            self.download_button.setIcon(load_icon("download_file.svg"))

        return QObject.event(obj, event)

    def update_file_size(self) -> None:
        try:
            self.file_size.setText(humanize_filesize(self.file.size))
        except Exception as e:
            logger.error(f"Could not update file size on FileWidget: {e}")
            self.file_size.setText("")

    def _set_file_state(self) -> None:
        if self.file.is_decrypted:
            logger.debug("Changing file {} state to decrypted/downloaded".format(self.uuid))
            self._set_file_name()
            self.download_button.hide()
            self.no_file_name.hide()
            self.export_button.show()
            self.middot.show()
            self.print_button.show()
            self.file_name.show()
            self.update_file_size()
        else:
            logger.debug("Changing file {} state to not downloaded".format(self.uuid))
            self.download_button.setText(_("DOWNLOAD"))

            # Ensure correct icon depending on mouse hover state.
            if self.download_button.underMouse():
                self.download_button.setIcon(load_icon("download_file_hover.svg"))
            else:
                self.download_button.setIcon(load_icon("download_file.svg"))

            self.download_button.setFont(self.file_buttons_font)
            self.download_button.show()

            # Reset stylesheet
            self.download_button.setStyleSheet("")
            self.download_button.setObjectName("FileWidget_download_button")
            self.download_button.setStyleSheet(self.DOWNLOAD_BUTTON_CSS)

            self.no_file_name.hide()
            self.export_button.hide()
            self.middot.hide()
            self.print_button.hide()
            self.file_name.hide()
            self.no_file_name.show()

    def _set_file_name(self) -> None:
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
    def _on_export_clicked(self) -> None:
        """
        Called when the export button is clicked.
        """
        if not self.controller.downloaded_file_exists(self.file):
            return

        self.export_dialog = ExportDialog(self.controller, self.uuid, self.file.filename)
        self.export_dialog.show()

    @pyqtSlot()
    def _on_print_clicked(self) -> None:
        """
        Called when the print button is clicked.
        """
        if not self.controller.downloaded_file_exists(self.file):
            return

        dialog = PrintDialog(self.controller, self.uuid, self.file.filename)
        dialog.exec()

    def _on_left_click(self) -> None:
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

    def start_button_animation(self) -> None:
        """
        Update the download button to the animated "downloading" state.
        """
        self.downloading = True
        self.download_animation.frameChanged.connect(self.set_button_animation_frame)
        self.download_animation.start()
        self.download_button.setText(_(" DOWNLOADING "))

        # Reset widget stylesheet
        self.download_button.setStyleSheet("")
        self.download_button.setObjectName("FileWidget_download_button_animating")
        self.download_button.setStyleSheet(self.DOWNLOAD_BUTTON_CSS)

    def set_button_animation_frame(self, frame_number: int) -> None:
        """
        Sets the download button's icon to the current frame of the spinner
        animation.
        """
        self.download_button.setIcon(QIcon(self.download_animation.currentPixmap()))

    def stop_button_animation(self) -> None:
        """
        Stops the download animation and restores the button to its default state.
        """
        self.download_animation.stop()
        self.file = self.controller.get_file(self.file.uuid)
        self._set_file_state()


class ModalDialog(QDialog):

    BUTTON_CSS = load_css("modal_dialog_button.css")
    ERROR_DETAILS_CSS = load_css("modal_dialog_error_details.css")

    MARGIN = 40
    NO_MARGIN = 0

    def __init__(self, show_header: bool = True, dangerous: bool = False) -> None:
        parent = QApplication.activeWindow()
        super().__init__(parent)
        self.setObjectName("ModalDialog")
        self.setModal(True)

        self.show_header = show_header
        self.dangerous = dangerous
        if self.dangerous:
            self.setProperty("class", "dangerous")

        # Widget for displaying error messages
        self.error_details = QLabel()
        self.error_details.setObjectName("ModalDialog_error_details")
        self.error_details.setStyleSheet(self.ERROR_DETAILS_CSS)
        self.error_details.setWordWrap(True)
        self.error_details.hide()

        # Body to display instructions and forms
        self.body = QLabel()
        self.body.setObjectName("ModalDialog_body")
        self.body.setWordWrap(True)
        self.body.setScaledContents(True)
        body_container = QWidget()
        self.body_layout = QVBoxLayout()
        self.body_layout.setContentsMargins(
            self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN
        )
        body_container.setLayout(self.body_layout)
        self.body_layout.addWidget(self.body)

        # Main widget layout
        layout = QVBoxLayout(self)
        layout.setContentsMargins(self.MARGIN, self.MARGIN, self.MARGIN, self.MARGIN)
        self.setLayout(layout)

        if self.show_header:
            # Header for icon and task title
            header_container = QWidget()
            header_container_layout = QHBoxLayout()
            header_container.setLayout(header_container_layout)
            self.header_icon = SvgLabel("blank.svg", svg_size=QSize(64, 64))
            self.header_icon.setObjectName("ModalDialog_header_icon")
            self.header_spinner = QPixmap()
            self.header_spinner_label = QLabel()
            self.header_spinner_label.setObjectName("ModalDialog_header_spinner")
            self.header_spinner_label.setMinimumSize(64, 64)
            self.header_spinner_label.setVisible(False)
            self.header_spinner_label.setPixmap(self.header_spinner)
            self.header = QLabel()
            self.header.setObjectName("ModalDialog_header")
            header_container_layout.addWidget(self.header_icon)
            header_container_layout.addWidget(self.header_spinner_label)
            header_container_layout.addWidget(self.header, alignment=Qt.AlignCenter)
            header_container_layout.addStretch()

            self.header_line = QWidget()
            self.header_line.setObjectName("ModalDialog_header_line")

            layout.addWidget(header_container)
            layout.addWidget(self.header_line)

        layout.addWidget(self.error_details)
        layout.addWidget(body_container)
        layout.addWidget(self.configure_buttons())

        # Activestate animation.
        self.button_animation = load_movie("activestate-wide.gif")
        self.button_animation.setScaledSize(QSize(32, 32))
        self.button_animation.frameChanged.connect(self.animate_activestate)

        # Header animation.
        self.header_animation = load_movie("header_animation.gif")
        self.header_animation.setScaledSize(QSize(64, 64))
        self.header_animation.frameChanged.connect(self.animate_header)

    def configure_buttons(self) -> QWidget:
        # Buttons to continue and cancel
        window_buttons = QWidget()
        window_buttons.setObjectName("ModalDialog_window_buttons")

        button_layout = QVBoxLayout()
        window_buttons.setLayout(button_layout)

        self.cancel_button = QPushButton(_("CANCEL"))
        self.cancel_button.setStyleSheet(self.BUTTON_CSS)
        self.cancel_button.clicked.connect(self.close)

        self.continue_button = QPushButton(_("CONTINUE"))
        self.continue_button.setStyleSheet(self.BUTTON_CSS)
        self.continue_button.setIconSize(QSize(21, 21))

        button_box = QDialogButtonBox(Qt.Horizontal)
        button_box.setObjectName("ModalDialog_button_box")

        if self.dangerous:
            self.cancel_button.setAutoDefault(True)
            self.continue_button.setDefault(False)
            self.cancel_button.setObjectName("ModalDialog_primary_button")
            self.continue_button.setObjectName("ModalDialog_cancel_button")
        else:
            self.cancel_button.setAutoDefault(False)
            self.continue_button.setDefault(True)
            self.cancel_button.setObjectName("ModalDialog_cancel_button")
            self.continue_button.setObjectName("ModalDialog_primary_button")

        button_box.addButton(self.cancel_button, QDialogButtonBox.ActionRole)
        button_box.addButton(self.continue_button, QDialogButtonBox.ActionRole)

        self.confirmation_label = QLabel()
        self.confirmation_label.setObjectName("ModalDialogConfirmation")
        button_layout.addWidget(self.confirmation_label, 0, Qt.AlignLeft | Qt.AlignBottom)

        button_layout.addWidget(button_box, alignment=Qt.AlignLeft)

        button_layout.setContentsMargins(
            self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN
        )

        return window_buttons

    def keyPressEvent(self, event: QKeyEvent) -> None:
        if event.key() == Qt.Key_Enter or event.key() == Qt.Key_Return:
            if self.cancel_button.hasFocus():
                self.cancel_button.click()
            else:
                self.continue_button.click()
        else:
            super().keyPressEvent(event)

    def animate_activestate(self) -> None:
        self.continue_button.setIcon(QIcon(self.button_animation.currentPixmap()))

    def animate_header(self) -> None:
        self.header_spinner_label.setPixmap(self.header_animation.currentPixmap())

    def start_animate_activestate(self) -> None:
        self.button_animation.start()
        self.continue_button.setText("")
        self.continue_button.setMinimumSize(QSize(142, 43))
        # Reset widget stylesheets
        self.continue_button.setStyleSheet("")
        self.continue_button.setObjectName("ModalDialog_primary_button_active")
        self.continue_button.setStyleSheet(self.BUTTON_CSS)
        self.error_details.setStyleSheet("")
        self.error_details.setObjectName("ModalDialog_error_details_active")
        self.error_details.setStyleSheet(self.ERROR_DETAILS_CSS)

    def start_animate_header(self) -> None:
        self.header_icon.setVisible(False)
        self.header_spinner_label.setVisible(True)
        self.header_animation.start()

    def stop_animate_activestate(self) -> None:
        self.continue_button.setIcon(QIcon())
        self.button_animation.stop()
        self.continue_button.setText(_("CONTINUE"))
        # Reset widget stylesheets
        self.continue_button.setStyleSheet("")
        self.continue_button.setObjectName("ModalDialog_primary_button")
        self.continue_button.setStyleSheet(self.BUTTON_CSS)
        self.error_details.setStyleSheet("")
        self.error_details.setObjectName("ModalDialog_error_details")
        self.error_details.setStyleSheet(self.ERROR_DETAILS_CSS)

    def stop_animate_header(self) -> None:
        self.header_icon.setVisible(True)
        self.header_spinner_label.setVisible(False)
        self.header_animation.stop()


class PrintDialog(ModalDialog):

    FILENAME_WIDTH_PX = 260

    def __init__(self, controller: Controller, file_uuid: str, file_name: str) -> None:
        super().__init__()

        self.controller = controller
        self.file_uuid = file_uuid
        self.file_name = SecureQLabel(
            file_name, wordwrap=False, max_length=self.FILENAME_WIDTH_PX
        ).text()
        self.error_status = ""  # Hold onto the error status we receive from the Export VM

        # Connect controller signals to slots
        self.controller.export.printer_preflight_success.connect(self._on_preflight_success)
        self.controller.export.printer_preflight_failure.connect(self._on_preflight_failure)

        # Connect parent signals to slots
        self.continue_button.setEnabled(False)
        self.continue_button.clicked.connect(self._run_preflight)

        # Dialog content
        self.starting_header = _(
            "Preparing to print:"
            "<br />"
            '<span style="font-weight:normal">{}</span>'.format(self.file_name)
        )
        self.ready_header = _(
            "Ready to print:"
            "<br />"
            '<span style="font-weight:normal">{}</span>'.format(self.file_name)
        )
        self.insert_usb_header = _("Connect USB printer")
        self.error_header = _("Printing failed")
        self.starting_message = _(
            "<h2>Managing printout risks</h2>"
            "<b>QR codes and web addresses</b>"
            "<br />"
            "Never type in and open web addresses or scan QR codes contained in printed "
            "documents without taking security precautions. If you are unsure how to "
            "manage this risk, please contact your administrator."
            "<br /><br />"
            "<b>Printer dots</b>"
            "<br />"
            "Any part of a printed page may contain identifying information "
            "invisible to the naked eye, such as printer dots. Please carefully "
            "consider this risk when working with or publishing scanned printouts."
        )
        self.insert_usb_message = _("Please connect your printer to a USB port.")
        self.generic_error_message = _("See your administrator for help.")

        self._show_starting_instructions()
        self.start_animate_header()
        self._run_preflight()

    def _show_starting_instructions(self) -> None:
        self.header.setText(self.starting_header)
        self.body.setText(self.starting_message)
        self.error_details.hide()
        self.adjustSize()

    def _show_insert_usb_message(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self._run_preflight)
        self.header.setText(self.insert_usb_header)
        self.body.setText(self.insert_usb_message)
        self.error_details.hide()
        self.adjustSize()

    def _show_generic_error_message(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self.close)
        self.continue_button.setText(_("DONE"))
        self.header.setText(self.error_header)
        self.body.setText(  # nosemgrep: semgrep.untranslated-gui-string
            "{}: {}".format(self.error_status, self.generic_error_message)
        )
        self.error_details.hide()
        self.adjustSize()

    @pyqtSlot()
    def _run_preflight(self) -> None:
        self.controller.run_printer_preflight_checks()

    @pyqtSlot()
    def _print_file(self) -> None:
        self.controller.print_file(self.file_uuid)
        self.close()

    @pyqtSlot()
    def _on_preflight_success(self) -> None:
        # If the continue button is disabled then this is the result of a background preflight check
        self.stop_animate_header()
        self.header_icon.update_image("printer.svg", svg_size=QSize(64, 64))
        self.header.setText(self.ready_header)
        if not self.continue_button.isEnabled():
            self.continue_button.clicked.disconnect()
            self.continue_button.clicked.connect(self._print_file)
            self.continue_button.setEnabled(True)
            self.continue_button.setFocus()
            return

        self._print_file()

    @pyqtSlot(object)
    def _on_preflight_failure(self, error: ExportError) -> None:
        self.stop_animate_header()
        self.header_icon.update_image("printer.svg", svg_size=QSize(64, 64))
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

    PASSPHRASE_LABEL_SPACING = 0.5
    NO_MARGIN = 0
    FILENAME_WIDTH_PX = 260

    def __init__(self, controller: Controller, file_uuid: str, file_name: str) -> None:
        super().__init__()

        self.controller = controller
        self.file_uuid = file_uuid
        self.file_name = SecureQLabel(
            file_name, wordwrap=False, max_length=self.FILENAME_WIDTH_PX
        ).text()
        self.error_status = ""  # Hold onto the error status we receive from the Export VM

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
            "Preparing to export:"
            "<br />"
            '<span style="font-weight:normal">{}</span>'.format(self.file_name)
        )
        self.ready_header = _(
            "Ready to export:"
            "<br />"
            '<span style="font-weight:normal">{}</span>'.format(self.file_name)
        )
        self.insert_usb_header = _("Insert encrypted USB drive")
        self.passphrase_header = _("Enter passphrase for USB drive")
        self.success_header = _("Export successful")
        self.error_header = _("Export failed")
        self.starting_message = _(
            "<h2>Understand the risks before exporting files</h2>"
            "<b>Malware</b>"
            "<br />"
            "This workstation lets you open files securely. If you open files on another "
            "computer, any embedded malware may spread to your computer or network. If you are "
            "unsure how to manage this risk, please print the file, or contact your "
            "administrator."
            "<br /><br />"
            "<b>Anonymity</b>"
            "<br />"
            "Files submitted by sources may contain information or hidden metadata that "
            "identifies who they are. To protect your sources, please consider redacting files "
            "before working with them on network-connected computers."
        )
        self.exporting_message = _("Exporting: {}").format(self.file_name)
        self.insert_usb_message = _(
            "Please insert one of the export drives provisioned specifically "
            "for the SecureDrop Workstation."
        )
        self.usb_error_message = _(
            "Either the drive is not encrypted or there is something else wrong with it."
        )
        self.passphrase_error_message = _("The passphrase provided did not work. Please try again.")
        self.generic_error_message = _("See your administrator for help.")
        self.continue_disabled_message = _(
            "The CONTINUE button will be disabled until the Export VM is ready"
        )
        self.success_message = _(
            "Remember to be careful when working with files outside of your Workstation machine."
        )

        # Passphrase Form
        self.passphrase_form = QWidget()
        self.passphrase_form.setObjectName("ExportDialog_passphrase_form")
        passphrase_form_layout = QVBoxLayout()
        passphrase_form_layout.setContentsMargins(
            self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN
        )
        self.passphrase_form.setLayout(passphrase_form_layout)
        passphrase_label = SecureQLabel(_("Passphrase"))
        font = QFont()
        font.setLetterSpacing(QFont.AbsoluteSpacing, self.PASSPHRASE_LABEL_SPACING)
        passphrase_label.setFont(font)
        self.passphrase_field = PasswordEdit(self)
        self.passphrase_field.setEchoMode(QLineEdit.Password)
        effect = QGraphicsDropShadowEffect(self)
        effect.setOffset(0, -1)
        effect.setBlurRadius(4)
        effect.setColor(QColor("#aaa"))
        self.passphrase_field.setGraphicsEffect(effect)
        passphrase_form_layout.addWidget(passphrase_label)
        passphrase_form_layout.addWidget(self.passphrase_field)
        self.body_layout.addWidget(self.passphrase_form)
        self.passphrase_form.hide()

        self._show_starting_instructions()
        self.start_animate_header()
        self._run_preflight()

    def _show_starting_instructions(self) -> None:
        self.header.setText(self.starting_header)
        self.body.setText(self.starting_message)
        self.adjustSize()

    def _show_passphrase_request_message(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self._export_file)
        self.header.setText(self.passphrase_header)
        self.continue_button.setText(_("SUBMIT"))
        self.header_line.hide()
        self.error_details.hide()
        self.body.hide()
        self.passphrase_field.setFocus()
        self.passphrase_form.show()
        self.adjustSize()

    def _show_passphrase_request_message_again(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self._export_file)
        self.header.setText(self.passphrase_header)
        self.error_details.setText(self.passphrase_error_message)
        self.continue_button.setText(_("SUBMIT"))
        self.header_line.hide()
        self.body.hide()
        self.error_details.show()
        self.passphrase_field.setFocus()
        self.passphrase_form.show()
        self.adjustSize()

    def _show_success_message(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self.close)
        self.header.setText(self.success_header)
        self.continue_button.setText(_("DONE"))
        self.body.setText(self.success_message)
        self.cancel_button.hide()
        self.error_details.hide()
        self.passphrase_form.hide()
        self.header_line.show()
        self.body.show()
        self.adjustSize()

    def _show_insert_usb_message(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self._run_preflight)
        self.header.setText(self.insert_usb_header)
        self.continue_button.setText(_("CONTINUE"))
        self.body.setText(self.insert_usb_message)
        self.error_details.hide()
        self.passphrase_form.hide()
        self.header_line.show()
        self.body.show()
        self.adjustSize()

    def _show_insert_encrypted_usb_message(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self._run_preflight)
        self.header.setText(self.insert_usb_header)
        self.error_details.setText(self.usb_error_message)
        self.continue_button.setText(_("CONTINUE"))
        self.body.setText(self.insert_usb_message)
        self.passphrase_form.hide()
        self.header_line.show()
        self.error_details.show()
        self.body.show()
        self.adjustSize()

    def _show_generic_error_message(self) -> None:
        self.continue_button.clicked.disconnect()
        self.continue_button.clicked.connect(self.close)
        self.continue_button.setText(_("DONE"))
        self.header.setText(self.error_header)
        self.body.setText(  # nosemgrep: semgrep.untranslated-gui-string
            "{}: {}".format(self.error_status, self.generic_error_message)
        )
        self.error_details.hide()
        self.passphrase_form.hide()
        self.header_line.show()
        self.body.show()
        self.adjustSize()

    @pyqtSlot()
    def _run_preflight(self) -> None:
        self.controller.run_export_preflight_checks()

    @pyqtSlot()
    def _export_file(self, checked: bool = False) -> None:
        self.start_animate_activestate()
        self.cancel_button.setEnabled(False)
        self.passphrase_field.setDisabled(True)
        self.controller.export_file_to_usb_drive(self.file_uuid, self.passphrase_field.text())

    @pyqtSlot()
    def _on_preflight_success(self) -> None:
        # If the continue button is disabled then this is the result of a background preflight check
        self.stop_animate_header()
        self.header_icon.update_image("savetodisk.svg", QSize(64, 64))
        self.header.setText(self.ready_header)
        if not self.continue_button.isEnabled():
            self.continue_button.clicked.disconnect()
            self.continue_button.clicked.connect(self._show_passphrase_request_message)
            self.continue_button.setEnabled(True)
            self.continue_button.setFocus()
            return

        self._show_passphrase_request_message()

    @pyqtSlot(object)
    def _on_preflight_failure(self, error: ExportError) -> None:
        self.stop_animate_header()
        self.header_icon.update_image("savetodisk.svg", QSize(64, 64))
        self._update_dialog(error.status)

    @pyqtSlot()
    def _on_export_success(self) -> None:
        self.stop_animate_activestate()
        self._show_success_message()

    @pyqtSlot(object)
    def _on_export_failure(self, error: ExportError) -> None:
        self.stop_animate_activestate()
        self.cancel_button.setEnabled(True)
        self.passphrase_field.setDisabled(False)
        self._update_dialog(error.status)

    def _update_dialog(self, error_status: str) -> None:
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


class DeleteSourceDialog(ModalDialog):
    """Used to confirm deletion of source accounts."""

    def __init__(self, source: Source, controller: Controller) -> None:
        super().__init__(show_header=False, dangerous=True)

        self.source = source
        self.controller = controller

        self.body.setText(self.make_body_text())

        self.continue_button.setText(_("YES, DELETE ENTIRE SOURCE ACCOUNT"))
        self.continue_button.clicked.connect(self.delete_source)

        self.confirmation_label.setText(_("Are you sure this is what you want?"))

        self.adjustSize()

    def make_body_text(self) -> str:
        message_tuple = (
            "<style>",
            "p {{white-space: nowrap;}}",
            "</style>",
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
            source="<b>{}</b>".format(self.source.journalist_designation)
        )

    @pyqtSlot()
    def delete_source(self) -> None:
        self.controller.delete_source(self.source)
        self.close()


class DeleteConversationDialog(ModalDialog):
    """
    Shown to confirm deletion of all content in a source conversation.
    """

    def __init__(self, source: Source, controller: Controller) -> None:
        super().__init__(show_header=False, dangerous=False)

        self.source = source
        self.controller = controller

        self.body.setText(self.make_body_text())

        self.continue_button.setText(_("YES, DELETE FILES AND MESSAGES"))
        self.continue_button.clicked.connect(self.delete_conversation)
        self.continue_button.setFocus()

        self.adjustSize()

    def make_body_text(self) -> str:
        files = 0
        messages = 0
        replies = 0
        for submission in self.source.collection:
            if isinstance(submission, Message):
                messages += 1
            if isinstance(submission, Reply):
                replies += 1
            elif isinstance(submission, File):
                files += 1

        message_tuple = (
            "<style>li {{line-height: 150%;}}</li></style>",
            "<p>",
            _(
                "You would like to delete {files_to_delete}, {replies_to_delete}, "
                "{messages_to_delete} from the source account for {source}?"
            ),
            "</p>",
            "<p>",
            _(
                "Preserving the account will retain its metadata, and the ability for {source} "
                "to log in to your SecureDrop again."
            ),
            "</p>",
        )

        files_to_delete = ngettext("one file", "{file_count} files", files).format(file_count=files)

        replies_to_delete = ngettext("one reply", "{reply_count} replies", replies).format(
            reply_count=replies
        )

        messages_to_delete = ngettext("one message", "{message_count} messages", messages).format(
            message_count=messages
        )

        source = "<b>{}</b>".format(self.source.journalist_designation)

        return "".join(message_tuple).format(
            files_to_delete=files_to_delete,
            messages_to_delete=messages_to_delete,
            replies_to_delete=replies_to_delete,
            source=source,
        )

    def exec(self) -> None:
        # Refresh counters
        self.body.setText(self.make_body_text())
        super().exec()

    @pyqtSlot()
    def delete_conversation(self) -> None:
        self.controller.delete_conversation(self.source)
        self.close()


class ConversationScrollArea(QScrollArea):

    MARGIN_LEFT = 38
    MARGIN_RIGHT = 20

    def __init__(self) -> None:
        super().__init__()

        self.setWidgetResizable(True)

        self.setObjectName("ConversationScrollArea")

        # Create the scroll area's widget
        conversation = QWidget()
        conversation.setObjectName("ConversationScrollArea_conversation")
        # The size policy for the scrollarea's widget needs a fixed height so that the speech
        # bubbles are aligned at the top rather than spreading out to fill the height of the
        # scrollarea.
        conversation.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        self.conversation_layout = QVBoxLayout()
        conversation.setLayout(self.conversation_layout)
        self.conversation_layout.setContentsMargins(self.MARGIN_LEFT, 0, self.MARGIN_RIGHT, 0)
        self.conversation_layout.setSpacing(0)

        # `conversation` is a child of this scroll area
        self.setWidget(conversation)

    def resizeEvent(self, event: QResizeEvent) -> None:
        """
        This is a workaround to the workaround for https://bugreports.qt.io/browse/QTBUG-85498.
        See comment in the adjust_width method for SpeechBubble.
        """
        super().resizeEvent(event)
        self.widget().setFixedWidth(event.size().width())

        for widget in self.findChildren(FileWidget):
            widget.adjust_width(self.widget().width())

        for widget in self.findChildren(SpeechBubble):
            widget.adjust_width(self.widget().width())

    def add_widget_to_conversation(
        self, index: int, widget: QWidget, alignment_flag: Qt.AlignmentFlag
    ) -> None:
        """
        Add `widget` to the scroll area's widget layout.
        """
        self.conversation_layout.insertWidget(index, widget, alignment=alignment_flag)

    def remove_widget_from_conversation(self, widget: QWidget) -> None:
        """
        Remove `widget` from the scroll area's widget layout.
        """
        self.conversation_layout.removeWidget(widget)


class DeletedConversationItemsMarker(QWidget):
    """
    Shown when earlier conversation items have been deleted.
    """

    TOP_MARGIN = 28
    BOTTOM_MARGIN = 4  # Add some spacing at the bottom between other widgets during scroll

    def __init__(self) -> None:
        super().__init__()

        self.hide()

        self.setObjectName("DeletedConversationItemsMarker")

        left_tear = SvgLabel("tear-left.svg", svg_size=QSize(196, 15))
        left_tear.setMinimumWidth(196)
        left_tear.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        deletion_message = QLabel(_("Earlier files and messages deleted."))
        deletion_message.setSizePolicy(QSizePolicy.Minimum, QSizePolicy.Fixed)
        deletion_message.setWordWrap(False)
        deletion_message.setObjectName("DeletedConversationItemsMessage")

        right_tear = SvgLabel("tear-right.svg", svg_size=QSize(196, 15))
        right_tear.setMinimumWidth(196)
        right_tear.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        layout = QGridLayout()
        layout.setContentsMargins(0, self.TOP_MARGIN, 0, self.BOTTOM_MARGIN)

        layout.addWidget(left_tear, 0, 0, Qt.AlignRight)
        layout.addWidget(deletion_message, 0, 1, Qt.AlignCenter)
        layout.addWidget(right_tear, 0, 2, Qt.AlignLeft)

        layout.setColumnStretch(0, 1)
        layout.setColumnStretch(1, 0)
        layout.setColumnStretch(2, 1)

        self.setLayout(layout)


class DeletedConversationMarker(QWidget):
    """
    Shown when all content in a conversation has been deleted.
    """

    def __init__(self) -> None:
        super().__init__()

        self.hide()

        self.setObjectName("DeletedConversationMarker")

        deletion_message = QLabel(_("Files and messages deleted\n for this source"))
        deletion_message.setWordWrap(True)
        deletion_message.setAlignment(Qt.AlignCenter)
        deletion_message.setObjectName("DeletedConversationMessage")

        tear = SvgLabel("tear-big.svg", svg_size=QSize(576, 8))
        tear.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        layout = QVBoxLayout()
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(20)

        layout.addStretch()
        layout.addWidget(deletion_message)
        layout.addWidget(tear)
        layout.addStretch()

        self.setLayout(layout)


class ConversationView(QWidget):
    """
    Renders a conversation.
    """

    conversation_updated = pyqtSignal()

    SCROLL_BAR_WIDTH = 15

    def __init__(self, source_db_object: Source, controller: Controller) -> None:
        super().__init__()

        self.source = source_db_object
        self.controller = controller

        # To hold currently displayed messages.
        self.current_messages = {}  # type: Dict[str, QWidget]

        self.setObjectName("ConversationView")

        # Set layout
        main_layout = QVBoxLayout()
        self.setLayout(main_layout)

        # Set margins and spacing
        main_layout.setContentsMargins(0, 0, 0, 0)
        main_layout.setSpacing(0)

        self.deleted_conversation_items_marker = DeletedConversationItemsMarker()
        self.deleted_conversation_marker = DeletedConversationMarker()
        main_layout.addWidget(self.deleted_conversation_items_marker)
        main_layout.addWidget(self.deleted_conversation_marker)

        self.scroll = ConversationScrollArea()

        # Flag to show if the current user has sent a reply. See issue #61.
        self.reply_flag = False

        # Completely unintuitive way to ensure the view remains scrolled to the bottom.
        sb = self.scroll.verticalScrollBar()
        sb.rangeChanged.connect(self.update_conversation_position)

        main_layout.addWidget(self.scroll)

        try:
            self.update_conversation(self.source.collection)
        except sqlalchemy.exc.InvalidRequestError as e:
            logger.debug("Error initializing ConversationView: %s", e)

    def update_deletion_markers(self, collection: list) -> None:
        if collection:
            self.scroll.show()
            if collection[0].file_counter > 1:
                self.deleted_conversation_marker.hide()
                self.deleted_conversation_items_marker.show()
        elif self.source.interaction_count > 0:
            self.deleted_conversation_items_marker.hide()
            self.scroll.hide()
            self.deleted_conversation_marker.show()

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
                    self.scroll.remove_widget_from_conversation(item_widget)
                    item_widget.index = index
                    if isinstance(item_widget, ReplyWidget):
                        self.scroll.add_widget_to_conversation(index, item_widget, Qt.AlignRight)
                    else:
                        self.scroll.add_widget_to_conversation(index, item_widget, Qt.AlignLeft)
                # Check if text in item has changed, then update the
                # widget to reflect this change.
                if not isinstance(item_widget, FileWidget):
                    if (
                        item_widget.message.text() != conversation_item.content
                    ) and conversation_item.content:
                        item_widget.message.setText(conversation_item.content)

                # TODO: Once the SDK supports the new /users endpoint, this code can be replaced so
                # that we can also update user accounts in the local db who have not sent replies.
                if isinstance(item_widget, ReplyWidget):
                    self.controller.session.refresh(conversation_item)
                    self.controller.session.refresh(conversation_item.journalist)
                    item_widget.sender = conversation_item.journalist
            else:
                # add a new item to be displayed.
                if isinstance(conversation_item, Message):
                    self.add_message(conversation_item, index)
                elif isinstance(conversation_item, (DraftReply, Reply)):
                    self.add_reply(conversation_item, conversation_item.journalist, index)
                else:
                    self.add_file(conversation_item, index)

        # If any items remain in current_conversation, they are no longer in the
        # source collection and should be removed from both the layout and the conversation
        # dict. Note that an item may be removed from the source collection if it is deleted
        # by another user (a journalist using the Web UI is able to delete individual
        # submissions).
        for item_widget in current_conversation.values():
            logger.debug("Deleting item: {}".format(item_widget.uuid))
            self.current_messages.pop(item_widget.uuid)
            item_widget.deleteLater()
            self.scroll.remove_widget_from_conversation(item_widget)

        self.update_deletion_markers(collection)
        self.conversation_updated.emit()

    def add_file(self, file: File, index: int) -> None:
        """
        Add a file from the source.
        """
        logger.debug("Adding file for {}".format(file.uuid))
        conversation_item = FileWidget(
            file.uuid,
            self.controller,
            self.controller.file_ready,
            self.controller.file_missing,
            index,
            self.scroll.widget().width(),
        )
        self.scroll.add_widget_to_conversation(index, conversation_item, Qt.AlignLeft)
        self.current_messages[file.uuid] = conversation_item
        self.conversation_updated.emit()

    def update_conversation_position(self, min_val: int, max_val: int) -> None:
        """
        Handler called when a new item is added to the conversation. Ensures
        it's scrolled to the bottom and thus visible.
        """
        if self.reply_flag and max_val > 0:
            self.scroll.verticalScrollBar().setValue(max_val)
            self.reply_flag = False

    def add_message(self, message: Message, index: int) -> None:
        """
        Add a message from the source.
        """
        conversation_item = MessageWidget(
            message.uuid,
            str(message),
            self.controller.message_ready,
            self.controller.message_download_failed,
            index,
            self.scroll.widget().width(),
            message.download_error is not None,
        )
        self.scroll.add_widget_to_conversation(index, conversation_item, Qt.AlignLeft)
        self.current_messages[message.uuid] = conversation_item
        self.conversation_updated.emit()

    def add_reply(self, reply: Union[DraftReply, Reply], sender: User, index: int) -> None:
        """
        Add a reply from a journalist to the source.
        """
        try:
            send_status = reply.send_status.name
        except AttributeError:
            send_status = "SUCCEEDED"  # TODO: Add and use success status in db.ReplySendStatusCodes

        if (
            self.controller.authenticated_user
            and self.controller.authenticated_user.id == reply.journalist_id
        ):
            sender_is_current_user = True
        else:
            sender_is_current_user = False

        conversation_item = ReplyWidget(
            self.controller,
            reply.uuid,
            str(reply),
            send_status,
            self.controller.reply_ready,
            self.controller.reply_download_failed,
            self.controller.reply_succeeded,
            self.controller.reply_failed,
            index,
            self.scroll.widget().width(),
            sender,
            sender_is_current_user,
            failed_to_decrypt=getattr(reply, "download_error", None) is not None,
        )

        self.scroll.add_widget_to_conversation(index, conversation_item, Qt.AlignRight)
        self.current_messages[reply.uuid] = conversation_item

    def add_reply_from_reply_box(self, uuid: str, content: str) -> None:
        """
        Add a reply from the reply box.
        """
        if not self.controller.authenticated_user:
            logger.error("User is no longer authenticated so cannot send reply.")
            return

        index = len(self.current_messages)
        conversation_item = ReplyWidget(
            self.controller,
            uuid,
            content,
            "PENDING",
            self.controller.reply_ready,
            self.controller.reply_download_failed,
            self.controller.reply_succeeded,
            self.controller.reply_failed,
            index,
            self.scroll.widget().width(),
            self.controller.authenticated_user,
            True,
        )
        self.scroll.add_widget_to_conversation(index, conversation_item, Qt.AlignRight)
        self.current_messages[uuid] = conversation_item

    def on_reply_sent(self, source_uuid: str, reply_uuid: str, reply_text: str) -> None:
        """
        Add the reply text sent from ReplyBoxWidget to the conversation.
        """
        self.reply_flag = True
        if source_uuid == self.source.uuid:
            self.add_reply_from_reply_box(reply_uuid, reply_text)
            try:
                self.update_deletion_markers(self.source.collection.copy())
            except sqlalchemy.exc.InvalidRequestError as e:
                # The only way we should get here is if
                # source.collection can't be populated, presumably
                # because it had never been loaded, and the source and
                # its conversation items were deleted between adding
                # the reply and updating deletion markers.
                logger.debug("Error in ConversationView.on_reply_sent: %s", e)


class SourceConversationWrapper(QWidget):
    """
    Wrapper for a source's conversation including the chat window, profile tab, and other
    per-source resources.
    """

    deleting_account = False
    deleting_conversation = False

    def __init__(self, source: Source, controller: Controller) -> None:
        super().__init__()

        self.setObjectName("SourceConversationWrapper")

        self.source = source
        self.source_uuid = source.uuid
        controller.conversation_deleted.connect(self.on_conversation_deleted)
        controller.conversation_deletion_failed.connect(self.on_conversation_deletion_failed)
        controller.source_deleted.connect(self.on_source_deleted)
        controller.source_deletion_failed.connect(self.on_source_deletion_failed)

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
        self.deletion_indicator = SourceDeletionIndicator()
        self.conversation_deletion_indicator = ConversationDeletionIndicator()

        # Add widgets
        layout.addWidget(self.conversation_title_bar)
        layout.addWidget(self.conversation_view)
        layout.addWidget(self.deletion_indicator)
        layout.addWidget(self.conversation_deletion_indicator)
        layout.addWidget(self.reply_box)

        # Connect reply_box to conversation_view
        self.reply_box.reply_sent.connect(self.conversation_view.on_reply_sent)
        self.conversation_view.conversation_updated.connect(self.on_conversation_updated)

    @pyqtSlot(str)
    def on_conversation_deleted(self, source_uuid: str) -> None:
        if self.source_uuid == source_uuid:
            self.start_conversation_deletion()

    @pyqtSlot(str)
    def on_conversation_deletion_failed(self, source_uuid: str) -> None:
        if self.source_uuid == source_uuid:
            self.end_conversation_deletion()

    @pyqtSlot()
    def on_conversation_updated(self) -> None:
        self.conversation_title_bar.update_timestamp()

    @pyqtSlot(str)
    def on_source_deleted(self, source_uuid: str) -> None:
        if self.source_uuid == source_uuid:
            self.start_account_deletion()

    @pyqtSlot(str)
    def on_source_deletion_failed(self, source_uuid: str) -> None:
        if self.source_uuid == source_uuid:
            self.end_account_deletion()

    def start_conversation_deletion(self) -> None:
        self.reply_box.setProperty("class", "deleting_conversation")
        self.deleting_conversation = True
        self.start_deletion()
        self.conversation_deletion_indicator.start()
        self.deletion_indicator.stop()

    def start_account_deletion(self) -> None:
        self.reply_box.setProperty("class", "deleting")
        self.deleting_account = True
        self.reply_box.text_edit.setText("")
        self.start_deletion()

        palette = QPalette()
        palette.setBrush(QPalette.Background, QBrush(QColor("#9495b9")))
        palette.setBrush(QPalette.Foreground, QBrush(QColor("#ffffff")))

        self.conversation_title_bar.setPalette(palette)
        self.conversation_title_bar.setAutoFillBackground(True)

        self.conversation_deletion_indicator.stop()
        self.deletion_indicator.start()

    def start_deletion(self) -> None:
        css = load_css("sdclient.css")
        self.reply_box.setStyleSheet(css)
        self.setStyleSheet(css)

        self.reply_box.text_edit.setDisabled(True)
        self.reply_box.text_edit.hide()
        self.reply_box.send_button.setDisabled(True)
        self.conversation_title_bar.setDisabled(True)
        self.conversation_view.hide()

    def end_conversation_deletion(self) -> None:
        self.deleting_conversation = False
        self.end_deletion()

    def end_account_deletion(self) -> None:
        self.deleting_account = False
        self.end_deletion()

    def end_deletion(self) -> None:
        self.reply_box.setProperty("class", "")
        css = load_css("sdclient.css")
        self.reply_box.setStyleSheet(css)
        self.setStyleSheet(css)

        self.reply_box.text_edit.setEnabled(True)
        self.reply_box.text_edit.show()
        self.reply_box.send_button.setEnabled(True)
        self.conversation_title_bar.setEnabled(True)
        self.conversation_view.show()

        self.conversation_deletion_indicator.stop()
        self.deletion_indicator.stop()


class ReplyBoxWidget(QWidget):
    """
    A textbox where a journalist can enter a reply.
    """

    reply_sent = pyqtSignal(str, str, str)

    def __init__(self, source: Source, controller: Controller) -> None:
        super().__init__()

        self.source = source
        self.controller = controller

        # Set css id
        self.setObjectName("ReplyBoxWidget")

        # Set layout
        main_layout = QVBoxLayout()
        self.setLayout(main_layout)

        # Set margins
        main_layout.setContentsMargins(0, 0, 0, 0)
        main_layout.setSpacing(0)

        # Create top horizontal line
        horizontal_line = QWidget()
        horizontal_line.setObjectName("ReplyBoxWidget_horizontal_line")
        horizontal_line.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        # Create replybox
        self.replybox = QWidget()
        self.replybox.setObjectName("ReplyBoxWidget_replybox")
        replybox_layout = QHBoxLayout(self.replybox)
        replybox_layout.setContentsMargins(32.6, 19, 27.3, 18)
        replybox_layout.setSpacing(0)

        # Create reply text box
        self.text_edit = ReplyTextEdit(self.source, self.controller)

        # Create reply send button (airplane)
        self.send_button = QPushButton()
        self.send_button.setObjectName("ReplyBoxWidget_send_button")
        self.send_button.clicked.connect(self.send_reply)
        send_button_icon = QIcon(load_image("send.svg"))
        send_button_icon.addPixmap(load_image("send-disabled.svg"), QIcon.Disabled)
        self.send_button.setIcon(send_button_icon)
        self.send_button.setIconSize(QSize(56.5, 47))
        self.send_button.setShortcut(QKeySequence("Ctrl+Return"))
        self.send_button.setDefault(True)

        # Set cursor.
        self.send_button.setCursor(QCursor(Qt.PointingHandCursor))

        # Add widgets to replybox
        replybox_layout.addWidget(self.text_edit)
        replybox_layout.addWidget(self.send_button, alignment=Qt.AlignBottom)

        # Ensure TAB order from text edit -> send button
        self.setTabOrder(self.text_edit, self.send_button)

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

    def set_logged_in(self) -> None:
        self.text_edit.set_logged_in()
        # Even if we are logged in, we cannot reply to a source if we do not
        # have a public key for it.
        if self.source.public_key:
            self.replybox.setEnabled(True)
            self.send_button.show()
        else:
            self.replybox.setEnabled(False)
            self.send_button.hide()

    def set_logged_out(self) -> None:
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
            self.text_edit.setText("")
            reply_uuid = str(uuid4())
            self.controller.send_reply(self.source.uuid, reply_uuid, reply_text)
            self.reply_sent.emit(self.source.uuid, reply_uuid, reply_text)

    @pyqtSlot(bool)
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

            if data == "syncing" and self.text_edit.hasFocus():
                self.refocus_after_sync = True
            elif data == "synced" and self.refocus_after_sync:
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

    def __init__(self, source: Source, controller: Controller) -> None:
        super().__init__()

        self.controller = controller
        self.source = source

        self.setObjectName("ReplyTextEdit")

        retain_space = self.sizePolicy()
        retain_space.setRetainSizeWhenHidden(True)
        self.setSizePolicy(retain_space)

        self.setVerticalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.setTabChangesFocus(True)  # Needed so we can TAB to send button.
        self.setCursor(QCursor(Qt.IBeamCursor))

        self.placeholder = ReplyTextEditPlaceholder(source.journalist_designation)
        self.placeholder.setParent(self)

        self.set_logged_in()

    def focusInEvent(self, e: QFocusEvent) -> None:
        # override default behavior: when reply text box is focused, the placeholder
        # disappears instead of only doing so when text is typed
        if self.toPlainText() == "":
            self.placeholder.hide()
        super(ReplyTextEdit, self).focusInEvent(e)

    def focusOutEvent(self, e: QFocusEvent) -> None:
        if self.toPlainText() == "":
            self.placeholder.show()
        super(ReplyTextEdit, self).focusOutEvent(e)

    def set_logged_in(self) -> None:
        if self.source.public_key:
            self.placeholder.show_signed_in()
            self.setEnabled(True)
        else:
            self.placeholder.show_signed_in_no_key()
            self.setEnabled(False)

    def set_logged_out(self) -> None:
        self.placeholder.show_signed_out()
        self.setEnabled(False)

    def setText(self, text: str) -> None:
        if text == "":
            self.placeholder.show()
        else:
            self.placeholder.hide()
        super(ReplyTextEdit, self).setPlainText(text)

    def resizeEvent(self, event: QResizeEvent) -> None:
        # Adjust available source label width to elide text when necessary
        self.placeholder.update_label_width(event.size().width())
        super().resizeEvent(event)


class ReplyTextEditPlaceholder(QWidget):

    # These values are used to determine the width that can be taken up by
    # the source designation as the widget is initialized or the window is
    # resized.
    INITIAL_MAX_WIDTH = 150
    RESERVED_WIDTH = 250

    # We allocate a fixed with to the source designation because its text is
    # dynamically resized, which otherwise causes Qt's layout engine to
    # incorrectly reposition it
    FIXED_LABEL_WIDTH = 800

    def __init__(self, source_name: str) -> None:
        super().__init__()

        # Set layout
        layout = QVBoxLayout()
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)
        self.setLayout(layout)

        # Signed in
        compose_a_reply_to = QLabel(_("Compose a reply to "))
        compose_a_reply_to.setObjectName("ReplyTextEditPlaceholder_text")
        self.source_name = source_name
        self.source_name_label = SecureQLabel(
            source_name, wordwrap=False, max_length=self.INITIAL_MAX_WIDTH
        )
        self.source_name_label.setObjectName("ReplyTextEditPlaceholder_bold_blue")
        self.source_name_label.setFixedWidth(self.FIXED_LABEL_WIDTH)
        self.signed_in = QWidget()
        signed_in_layout = QHBoxLayout()
        signed_in_layout.setSpacing(0)
        self.signed_in.setLayout(signed_in_layout)
        signed_in_layout.addWidget(compose_a_reply_to)
        signed_in_layout.addWidget(self.source_name_label)
        self.signed_in.hide()

        # Awaiting key
        awaiting_key = QLabel(_("Awaiting encryption key"))
        awaiting_key.setObjectName("ReplyTextEditPlaceholder_bold_blue")
        from_server = QLabel(_(" from server to enable replies"))
        from_server.setObjectName("ReplyTextEditPlaceholder_text")
        self.signed_in_no_key = QWidget()
        signed_in_no_key_layout = QHBoxLayout()
        signed_in_no_key_layout.setSpacing(0)
        self.signed_in_no_key.setLayout(signed_in_no_key_layout)
        signed_in_no_key_layout.addWidget(awaiting_key)
        signed_in_no_key_layout.addWidget(from_server)
        self.signed_in_no_key.hide()

        # Signed out
        sign_in = QLabel(_("Sign in"))
        sign_in.setObjectName("ReplyTextEditPlaceholder_bold_blue")
        to_compose_reply = QLabel(_(" to compose or send a reply"))
        to_compose_reply.setObjectName("ReplyTextEditPlaceholder_text")
        self.signed_out = QWidget()
        signed_out_layout = QHBoxLayout()
        signed_out_layout.setSpacing(0)
        self.signed_out.setLayout(signed_out_layout)
        signed_out_layout.addWidget(sign_in)
        signed_out_layout.addWidget(to_compose_reply)
        signed_out_layout.addStretch()
        self.signed_out.hide()

        layout.addWidget(self.signed_in)
        layout.addWidget(self.signed_in_no_key)
        layout.addWidget(self.signed_out)

    def show_signed_in(self) -> None:
        self.signed_in_no_key.hide()
        self.signed_in.show()
        self.signed_out.hide()

    def show_signed_in_no_key(self) -> None:
        self.signed_in_no_key.show()
        self.signed_in.hide()
        self.signed_out.hide()

    def show_signed_out(self) -> None:
        self.signed_in_no_key.hide()
        self.signed_in.hide()
        self.signed_out.show()

    def update_label_width(self, width: int) -> None:
        if width > self.RESERVED_WIDTH:
            # Ensure source designations are elided with "..." if needed per
            # current container size
            self.source_name_label.max_length = width - self.RESERVED_WIDTH
            self.source_name_label.setText(self.source_name)


class SourceMenu(QMenu):
    """Renders menu having various operations.

    This menu provides below functionality via menu actions:

    1. Delete source

    Note: At present this only supports "delete" operation.
    """

    SOURCE_MENU_CSS = load_css("source_menu.css")

    def __init__(self, source: Source, controller: Controller) -> None:
        super().__init__()
        self.source = source
        self.controller = controller

        self.setStyleSheet(self.SOURCE_MENU_CSS)
        separator_font = QFont()
        separator_font.setLetterSpacing(QFont.AbsoluteSpacing, 2)
        separator_font.setBold(True)

        delete_section = self.addSection(_("DELETE"))
        delete_section.setFont(separator_font)

        self.addAction(DeleteConversationAction(self.source, self, self.controller))
        self.addAction(DeleteSourceAction(self.source, self, self.controller))


class DeleteSourceAction(QAction):
    """Use this action to delete the source record."""

    def __init__(self, source: Source, parent: SourceMenu, controller: Controller) -> None:
        self.source = source
        self.controller = controller
        self.text = _("Entire source account")

        super().__init__(self.text, parent)

        self.confirmation_dialog = DeleteSourceDialog(self.source, self.controller)
        self.triggered.connect(self.trigger)

    def trigger(self) -> None:
        if self.controller.api is None:
            self.controller.on_action_requiring_login()
        else:
            self.confirmation_dialog.exec()


class DeleteConversationAction(QAction):
    """Use this action to delete a source's submissions and replies."""

    def __init__(self, source: Source, parent: SourceMenu, controller: Controller) -> None:
        self.source = source
        self.controller = controller
        self.text = _("Files and messages")

        super().__init__(self.text, parent)

        self.confirmation_dialog = DeleteConversationDialog(self.source, self.controller)
        self.triggered.connect(self.trigger)

    def trigger(self) -> None:
        if self.controller.api is None:
            self.controller.on_action_requiring_login()
        else:
            self.confirmation_dialog.exec()


class SourceMenuButton(QToolButton):
    """An ellipse based source menu button.

    This button is responsible for launching the source menu on click.
    """

    def __init__(self, source: Source, controller: Controller) -> None:
        super().__init__()
        self.controller = controller
        self.source = source

        self.setObjectName("SourceMenuButton")

        self.setIcon(load_icon("ellipsis.svg"))
        self.setIconSize(QSize(22, 33))  # Make it taller than the svg viewBox to increase hitbox

        self.menu = SourceMenu(self.source, self.controller)
        self.setMenu(self.menu)

        self.setPopupMode(QToolButton.InstantPopup)
        # Set cursor.
        self.setCursor(QCursor(Qt.PointingHandCursor))


class TitleLabel(QLabel):
    """The title for a conversation."""

    def __init__(self, text: str) -> None:
        super().__init__(_(text))

        # Set CSS id
        self.setObjectName("TitleLabel")


class LastUpdatedLabel(QLabel):
    """Time the conversation was last updated."""

    def __init__(self, last_updated):  # type: ignore [no-untyped-def]
        super().__init__(last_updated)

        # Set CSS id
        self.setObjectName("LastUpdatedLabel")


class SourceProfileShortWidget(QWidget):
    """A widget for displaying short view for Source.

    It contains below information.
    1. Journalist designation
    2. A menu to perform various operations on Source.
    """

    MARGIN_LEFT = 25
    MARGIN_RIGHT = 17
    VERTICAL_MARGIN = 14

    def __init__(self, source: Source, controller: Controller) -> None:
        super().__init__()

        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        self.source = source
        self.controller = controller

        # Set layout
        layout = QVBoxLayout()
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)
        self.setLayout(layout)

        # Create header
        header = QWidget()
        header_layout = QHBoxLayout(header)
        header_layout.setContentsMargins(
            self.MARGIN_LEFT, self.VERTICAL_MARGIN, self.MARGIN_RIGHT, self.VERTICAL_MARGIN
        )
        title = TitleLabel(self.source.journalist_designation)
        self.updated = LastUpdatedLabel(_(arrow.get(self.source.last_updated).format("MMM D")))
        menu = SourceMenuButton(self.source, self.controller)
        header_layout.addWidget(title, alignment=Qt.AlignLeft)
        header_layout.addStretch()
        header_layout.addWidget(self.updated, alignment=Qt.AlignRight)
        header_layout.addWidget(menu, alignment=Qt.AlignRight)

        # Create horizontal line
        horizontal_line = QWidget()
        horizontal_line.setObjectName("SourceProfileShortWidget_horizontal_line")
        horizontal_line.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        # Add widgets
        layout.addWidget(header)
        layout.addWidget(horizontal_line)

    def update_timestamp(self) -> None:
        """
        Ensure the timestamp is always kept up to date with the latest activity
        from the source.
        """
        self.updated.setText(_(arrow.get(self.source.last_updated).format("MMM D")))
