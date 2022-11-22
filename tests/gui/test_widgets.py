"""
Make sure the UI widgets are configured correctly and work as expected.
"""
import math
import random
from datetime import datetime
from gettext import gettext as _
from unittest.mock import Mock, PropertyMock

import arrow
import sqlalchemy
import sqlalchemy.orm.exc
from PyQt5.QtCore import QEvent, QSize, Qt
from PyQt5.QtGui import QFocusEvent, QMovie, QResizeEvent
from PyQt5.QtTest import QTest
from PyQt5.QtWidgets import QVBoxLayout, QWidget
from sqlalchemy.orm import attributes, scoped_session, sessionmaker

from securedrop_client import db, logic, storage
from securedrop_client.app import threads
from securedrop_client.gui.source import DeleteSourceDialog
from securedrop_client.gui.widgets import (
    ActivityStatusBar,
    ConversationView,
    EmptyConversationView,
    ErrorStatusBar,
    FileWidget,
    LeftPane,
    LoginButton,
    MainView,
    MessageWidget,
    ReplyBoxWidget,
    ReplyTextEdit,
    ReplyTextEditPlaceholder,
    ReplyWidget,
    SecureQLabel,
    SenderIcon,
    SourceConversationWrapper,
    SourceList,
    SourceListWidgetItem,
    SourceMenu,
    SourcePreview,
    SourceProfileShortWidget,
    SourceWidget,
    SpeechBubble,
    StarToggleButton,
    SyncIcon,
    TopPane,
    UserButton,
    UserIconLabel,
    UserMenu,
    UserProfile,
)
from tests import factory
from tests.helper import app  # noqa: F401


def test_TopPane_init(mocker):
    """
    Ensure the TopPane instance is correctly set up.
    """
    tp = TopPane()
    file_path = tp.sync_icon.sync_animation.fileName()
    filename = file_path[file_path.rfind("/") + 1 :]
    assert filename == "sync_disabled.gif"


def test_TopPane_setup(mocker):
    """
    Calling setup calls setup for SyncIcon.
    """
    tp = TopPane()
    tp.sync_icon = mocker.MagicMock()
    mock_controller = mocker.MagicMock()

    tp.setup(mock_controller)

    tp.sync_icon.setup.assert_called_once_with(mock_controller)


def test_TopPane_set_logged_in(mocker):
    """
    Calling set_logged_in calls enable on TopPane.
    """
    tp = TopPane()
    tp.sync_icon = mocker.MagicMock()

    tp.set_logged_in()

    tp.sync_icon.enable.assert_called_once_with()


def test_TopPane_set_logged_out(mocker):
    """
    Calling set_logged_out calls disable on SyncIcon.
    """
    tp = TopPane()
    tp.sync_icon = mocker.MagicMock()

    tp.set_logged_out()

    tp.sync_icon.disable.assert_called_once_with()


def test_TopPane_update_activity_status(mocker):
    """
    Calling update_activity_status calls update_message on ActivityStatusBar.
    """
    tp = TopPane()
    tp.activity_status_bar = mocker.MagicMock()

    tp.update_activity_status(message="test message", duration=5)

    tp.activity_status_bar.update_message.assert_called_once_with("test message", 5)


def test_TopPane_update_error_status(mocker):
    """
    Calling update_error_status calls update_message on ErrorStatusBar.
    """
    tp = TopPane()
    tp.error_status_bar = mocker.MagicMock()

    tp.update_error_status(message="test message", duration=5)

    tp.error_status_bar.update_message.assert_called_once_with("test message", 5)


def test_TopPane_clear_error_status(mocker):
    """
    Calling clear_error_status calls clear_message.
    """
    tp = TopPane()
    tp.error_status_bar = mocker.MagicMock()

    tp.clear_error_status()

    tp.error_status_bar.clear_message.assert_called_once_with()


def test_LeftPane_init(mocker):
    """
    Ensure the LeftPane instance is correctly set up.
    """
    lp = LeftPane()
    lp.user_profile = mocker.MagicMock()
    assert lp.user_profile.isHidden()


def test_LeftPane_setup(mocker):
    """
    Calling setup calls setup for UserProfile.
    """
    lp = LeftPane()
    lp.user_profile = mocker.MagicMock()
    mock_window = mocker.MagicMock()
    mock_controller = mocker.MagicMock()

    lp.setup(mock_window, mock_controller)

    lp.user_profile.setup.assert_called_once_with(mock_window, mock_controller)


def test_LeftPane_set_logged_in_as(mocker):
    """
    When a user is logged in check that buttons and menus are in the correct state.
    """
    lp = LeftPane()
    lp.user_profile = mocker.MagicMock()
    user = mocker.MagicMock()

    lp.set_logged_in_as(user)

    lp.user_profile.show.assert_called_once_with()
    lp.user_profile.set_user.assert_called_once_with(user)


def test_LeftPane_set_logged_out(mocker):
    """
    When a user is logged out check that buttons and menus are in the correct state.
    """
    lp = LeftPane()
    lp.user_profile = mocker.MagicMock()

    lp.set_logged_out()

    lp.user_profile.hide.assert_called_once_with()


def test_SyncIcon_init(mocker):
    sync_icon = SyncIcon()
    file_path = sync_icon.sync_animation.fileName()
    filename = file_path[file_path.rfind("/") + 1 :]
    assert filename == "sync_disabled.gif"


def test_SyncIcon_init_starts_animation(mocker):
    movie = QMovie()
    movie.start = mocker.MagicMock()
    mocker.patch("securedrop_client.gui.widgets.load_movie", return_value=movie)

    sync_icon = SyncIcon()

    sync_icon.sync_animation.start.assert_called_once_with()


def test_SyncIcon_setup(mocker):
    """
    Calling setup stores reference to controller, which will later be used to update sync icon on
    syncing event.
    """
    sync_icon = SyncIcon()
    controller = mocker.MagicMock()

    sync_icon.setup(controller)

    assert sync_icon.controller == controller


def test_SyncIcon_enable(mocker):
    sync_icon = SyncIcon()

    sync_icon.enable()

    file_path = sync_icon.sync_animation.fileName()
    filename = file_path[file_path.rfind("/") + 1 :]
    assert filename == "sync.gif"


def test_SyncIcon_enable_starts_animation(mocker):
    movie = QMovie()
    movie.start = mocker.MagicMock()
    mocker.patch("securedrop_client.gui.widgets.load_movie", return_value=movie)

    sync_icon = SyncIcon()
    sync_icon.enable()

    sync_icon.sync_animation.start.assert_called_with()


def test_SyncIcon_disable(mocker):
    sync_icon = SyncIcon()

    sync_icon.disable()

    file_path = sync_icon.sync_animation.fileName()
    filename = file_path[file_path.rfind("/") + 1 :]
    assert filename == "sync_disabled.gif"


def test_SyncIcon_disable_starts_animation(mocker):
    movie = QMovie()
    movie.start = mocker.MagicMock()
    mocker.patch("securedrop_client.gui.widgets.load_movie", return_value=movie)

    sync_icon = SyncIcon()
    sync_icon.disable()

    sync_icon.sync_animation.start.assert_called_with()


def test_SyncIcon__on_sync_started(mocker):
    """
    Sync icon becomes active when it receives the `syncing` signal.
    """
    sync_icon = SyncIcon()

    sync_icon._on_sync_started(mocker.MagicMock())

    file_path = sync_icon.sync_animation.fileName()
    filename = file_path[file_path.rfind("/") + 1 :]
    assert filename == "sync_active.gif"


def test_SyncIcon__on_sync_succeeded(mocker):
    """
    Sync icon becomes "inactive" when it receives the `synced` signal.
    """
    sync_icon = SyncIcon()

    sync_icon._on_sync_succeeded()

    file_path = sync_icon.sync_animation.fileName()
    filename = file_path[file_path.rfind("/") + 1 :]
    assert filename == "sync.gif"


def test_ErrorStatusBar_clear_error_status(mocker):
    """
    Calling clear_error_status calls clear_message.
    """
    esb = ErrorStatusBar()
    esb.status_bar = mocker.MagicMock()

    esb.clear_message()

    esb.status_bar.clearMessage.assert_called_once_with()


def test_ErrorStatusBar_update_message(mocker):
    """
    Calling update_message updates the message of the QStatusBar and starts the a timer for the
    given duration.
    """
    esb = ErrorStatusBar()
    esb.status_bar = mocker.MagicMock()
    esb.status_timer = mocker.MagicMock()

    esb.update_message(message="test message", duration=123)

    esb.status_bar.showMessage.assert_called_once_with("test message", 123)
    esb.status_timer.start.assert_called_once_with(123)


def test_ErrorStatusBar_hide(mocker):
    esb = ErrorStatusBar()
    esb.vertical_bar = mocker.MagicMock()
    esb.label = mocker.MagicMock()
    esb.status_bar = mocker.MagicMock()

    esb._hide()

    esb.vertical_bar.hide.assert_called_once_with()
    esb.label.hide.assert_called_once_with()
    esb.status_bar.hide.assert_called_once_with()


def test_ErrorStatusBar_show(mocker):
    esb = ErrorStatusBar()
    esb.vertical_bar = mocker.MagicMock()
    esb.label = mocker.MagicMock()
    esb.status_bar = mocker.MagicMock()

    esb._show()

    esb.vertical_bar.show.assert_called_once_with()
    esb.label.show.assert_called_once_with()
    esb.status_bar.show.assert_called_once_with()


def test_ErrorStatusBar_on_status_timeout(mocker):
    esb = ErrorStatusBar()
    esb._on_status_timeout()
    assert esb.isHidden()


def test_ActivityStatusBar_update_message(mocker):
    """
    Calling update_message updates the message of the QStatusBar.
    """
    asb = ActivityStatusBar()
    asb.update_message(message="test message", duration=123)
    assert asb.currentMessage() == "test message"


def test_UserProfile_setup(mocker):
    up = UserProfile()
    up.user_button = mocker.MagicMock()
    up.login_button = mocker.MagicMock()
    window = mocker.MagicMock()
    controller = mocker.MagicMock()

    up.setup(window, controller)

    up.user_button.setup.assert_called_once_with(controller)
    up.login_button.setup.assert_called_once_with(window)
    up.controller.update_authenticated_user.connect.assert_called_once_with(
        up._on_update_authenticated_user
    )


def test_UserProfile__on_update_authenticated_user(mocker):
    up = UserProfile()
    up.set_user = mocker.MagicMock()
    user = factory.User(firstname="firstname_mock", lastname="lastname_mock")

    up._on_update_authenticated_user(user)

    up.set_user.assert_called_once_with(user)


def test_UserProfile_set_user(mocker):
    up = UserProfile()
    up.user_icon = mocker.MagicMock()
    up.user_button = mocker.MagicMock()
    user = factory.User(firstname="firstname_mock", lastname="lastname_mock")

    up.set_user(user)

    up.user_icon.setText.assert_called_with("fl")
    up.user_button.set_username.assert_called_with("firstname_mock lastname_mock")


def test_UserProfile_set_user_with_only_username(mocker):
    up = UserProfile()
    up.user_icon = mocker.MagicMock()
    up.user_button = mocker.MagicMock()
    user = factory.User(username="dellsberg", firstname=None, lastname=None)

    up.set_user(user)

    up.user_icon.setText.assert_called_with("de")
    up.user_button.set_username.assert_called_with("dellsberg")


def test_UserProfile_show(mocker):
    up = UserProfile()
    up.user_icon = mocker.MagicMock()
    up.user_button = mocker.MagicMock()
    up.login_button = mocker.MagicMock()

    up.show()

    up.login_button.hide.assert_called_once_with()
    up.user_icon.show.assert_called_once_with()
    up.user_button.show.assert_called_once_with()


def test_UserProfile_hide(mocker):
    up = UserProfile()
    up.user_icon = mocker.MagicMock()
    up.user_button = mocker.MagicMock()
    up.login_button = mocker.MagicMock()

    up.hide()

    up.user_icon.hide.assert_called_once_with()
    up.user_button.hide.assert_called_once_with()
    up.login_button.show.assert_called_once_with()


def test_UserIconLabel_clicks(mocker):
    uil = UserIconLabel()
    uil.clicked = mocker.MagicMock()
    uil.mousePressEvent(None)
    uil.clicked.emit.assert_called_once_with()


def test_UserButton_setup(mocker):
    ub = UserButton()
    ub.menu = mocker.MagicMock()
    controller = mocker.MagicMock()

    ub.setup(controller)

    ub.menu.setup.assert_called_once_with(controller)


def test_UserButton_set_username():
    ub = UserButton()
    ub.set_username("test_username")
    ub.text() == "test_username"


def test_UserButton_set_long_username(mocker):
    ub = UserButton()
    ub.setToolTip = mocker.MagicMock()
    ub.set_username("test_username_that_is_very_very_long")
    ub.setToolTip.assert_called_once_with("test_username_that_is_very_very_long")


def test_UserMenu_setup(mocker):
    um = UserMenu()
    controller = mocker.MagicMock()

    um.setup(controller)

    assert um.controller == controller


def test_UserMenu_on_logout_triggered(mocker):
    um = UserMenu()
    um.controller = mocker.MagicMock()

    um._on_logout_triggered()

    um.controller.logout.assert_called_once_with()


def test_UserMenu_on_item_selected(mocker):
    um = UserMenu()
    um.controller = mocker.MagicMock()

    um.actions()[0].trigger()

    um.controller.logout.assert_called_once_with()


def test_LoginButton_init(mocker):
    lb = LoginButton()
    assert lb.text() == "SIGN IN"


def test_LoginButton_setup(mocker):
    lb = LoginButton()
    window = mocker.MagicMock()
    lb.setup(window)
    lb.window = window


def test_Loginbutton_on_clicked(mocker):
    lb = LoginButton()
    lb.window = mocker.MagicMock()
    lb._on_clicked()
    lb.window.show_login.assert_called_once_with()


def test_MainView_init():
    """
    Ensure the MainView instance is correctly set up.
    """
    mv = MainView(None)
    assert isinstance(mv.source_list, SourceList)
    assert isinstance(mv.view_holder, QWidget)


def test_MainView_setup(mocker):
    mv = MainView(None)
    mv.source_list = mocker.MagicMock()
    controller = mocker.MagicMock()

    mv.setup(controller)

    assert mv.controller == controller
    mv.source_list.setup.assert_called_once_with(controller)


def test_MainView_show_sources_with_none_selected(mocker):
    """
    Ensure the sources list is passed to the source list widget to be updated.
    """
    mv = MainView(None)

    # Set up SourceList so that SourceList.get_selected_source() returns a source
    mv.source_list = SourceList()
    source_widget = SourceWidget(
        mocker.MagicMock(), factory.Source(uuid="stub_uuid"), mocker.MagicMock(), mocker.MagicMock()
    )
    source_item = SourceListWidgetItem(mv.source_list)
    mv.source_list.setItemWidget(source_item, source_widget)
    mv.source_list.source_items["stub_uuid"] = source_item
    mocker.patch.object(mv.source_list, "update")

    mv.empty_conversation_view = mocker.MagicMock()

    mv.show_sources([1, 2, 3])

    mv.source_list.update.assert_called_once_with([1, 2, 3])
    mv.empty_conversation_view.show_no_source_selected_message.assert_called_once_with()
    mv.empty_conversation_view.show.assert_called_once_with()


def test_MainView_show_sources_from_cold_start(mocker):
    """
    Ensure the initial_update is called if no sources exist in the UI.
    """
    mv = MainView(None)
    mv.source_list = mocker.MagicMock()
    mv.source_list.source_items = {}
    mv.empty_conversation_view = mocker.MagicMock()

    mv.show_sources([])

    mv.source_list.initial_update.assert_called_once_with([])


def test_MainView_show_sources_with_no_sources_at_all(mocker):
    """
    Ensure the sources list is passed to the source list widget to be updated.
    """
    mv = MainView(None)
    mv.source_list = mocker.MagicMock()
    mv.empty_conversation_view = mocker.MagicMock()

    mv.show_sources([])

    mv.source_list.update.assert_called_once_with([])
    mv.empty_conversation_view.show_no_sources_message.assert_called_once_with()
    mv.empty_conversation_view.show.assert_called_once_with()


def test_MainView_show_sources_when_sources_are_deleted(mocker):
    """
    Ensure that show_sources also deletes the SourceConversationWrapper for a deleted source.
    """
    mv = MainView(None)
    mv.source_list = mocker.MagicMock()
    mv.empty_conversation_view = mocker.MagicMock()
    mv.source_list.update = mocker.MagicMock(return_value=[])
    mv.delete_conversation = mocker.MagicMock()

    mv.show_sources([1, 2, 3, 4])

    mv.source_list.update = mocker.MagicMock(return_value=[4])

    mv.show_sources([1, 2, 3])

    mv.delete_conversation.assert_called_once_with(4)


def test_MainView_delete_conversation_when_conv_wrapper_exists(mocker):
    """
    Ensure SourceConversationWrapper is deleted if it exists.
    """
    source = factory.Source(uuid="123")
    conversation_wrapper = SourceConversationWrapper(source, mocker.MagicMock())
    conversation_wrapper.deleteLater = mocker.MagicMock()
    mv = MainView(None)
    mv.source_conversations = {}
    mv.source_conversations["123"] = conversation_wrapper

    mv.delete_conversation("123")

    conversation_wrapper.deleteLater.assert_called_once_with()
    assert mv.source_conversations == {}


def test_MainView_delete_conversation_when_conv_wrapper_does_not_exist(mocker):
    """
    Ensure that delete_conversation throws no exception if the SourceConversationWrapper
    does not exist.
    """
    source_uuid = "foo"
    mv = MainView(None)
    mv.source_conversations = {}

    mv.delete_conversation(source_uuid)

    assert mv.source_conversations == {}


def test_MainView_on_source_changed(mocker):
    """
    Ensure set_conversation is called when source changes.
    """
    mv = MainView(None)
    mv.set_conversation = mocker.MagicMock()
    mv.source_list = mocker.MagicMock()
    mv.source_list.get_selected_source = mocker.MagicMock(return_value=factory.Source())
    mv.controller = mocker.MagicMock(is_authenticated=True)
    mocker.patch("securedrop_client.gui.widgets.source_exists", return_value=True)
    scw = mocker.MagicMock()
    mocker.patch("securedrop_client.gui.widgets.SourceConversationWrapper", return_value=scw)

    mv.on_source_changed()

    mv.source_list.get_selected_source.assert_called_once_with()
    mv.set_conversation.assert_called_once_with(scw)


def test_MainView_on_source_changed_does_not_raise_InvalidRequestError(mocker):
    """
    If the source no longer exists in the local data store, ensure we just log and do not raise
    an exception.
    """
    mv = MainView(None)
    mv.set_conversation = mocker.MagicMock()
    mv.source_list = mocker.MagicMock()
    mv.source_list.get_selected_source = mocker.MagicMock(return_value=factory.Source())
    mv.controller = mocker.MagicMock(is_authenticated=True)
    ex = sqlalchemy.exc.InvalidRequestError()
    mv.controller.session.refresh.side_effect = ex

    mocker.patch("securedrop_client.gui.widgets.source_exists", return_value=True)
    scw = mocker.MagicMock()
    mocker.patch("securedrop_client.gui.widgets.SourceConversationWrapper", return_value=scw)
    mock_logger = mocker.MagicMock()
    mocker.patch("securedrop_client.gui.widgets.logger", mock_logger)

    mv.on_source_changed()

    assert mock_logger.debug.call_count == 1


def test_MainView_on_source_changed_when_source_no_longer_exists(mocker):
    """
    Test that conversation for a source is cleared when the source no longer exists.
    """
    mv = MainView(None)
    mv.set_conversation = mocker.MagicMock()
    mv.source_list = mocker.MagicMock()
    mv.source_list.get_selected_source = mocker.MagicMock(return_value=None)

    mv.on_source_changed()

    mv.source_list.get_selected_source.assert_called_once_with()
    mv.set_conversation.assert_not_called()


def test_MainView_on_source_changed_updates_conversation_view(mocker, session):
    """
    Test that the source collection is displayed in the conversation view.
    """
    mv = MainView(None)
    # mv.source_list = mocker.MagicMock()
    mv.controller = mocker.MagicMock(is_authenticated=True)
    source = factory.Source()
    session.add(source)
    file = factory.File(source=source, filename="0-mock-doc.gpg")
    message = factory.Message(source=source, filename="0-mock-msg.gpg")
    reply = factory.Reply(source=source, filename="0-mock-reply.gpg")
    session.add(file)
    session.add(message)
    session.add(reply)
    session.commit()
    source_selected = mocker.patch("securedrop_client.gui.widgets.SourceList.source_selected")
    mocker.patch(
        "securedrop_client.gui.widgets.SourceList.get_selected_source", return_value=source
    )
    add_message_fn = mocker.patch(
        "securedrop_client.gui.widgets.ConversationView.add_message", new=mocker.Mock()
    )
    add_reply_fn = mocker.patch(
        "securedrop_client.gui.widgets.ConversationView.add_reply", new=mocker.Mock()
    )
    add_file_fn = mocker.patch(
        "securedrop_client.gui.widgets.ConversationView.add_file", new=mocker.Mock()
    )

    mv.on_source_changed()

    source_selected.emit.assert_called_once_with(source.uuid)
    mv.controller.mark_seen.assert_called_once_with(source)
    assert add_message_fn.call_count == 1
    assert add_reply_fn.call_count == 1
    assert add_file_fn.call_count == 1


def test_MainView_on_source_changed_SourceConversationWrapper_is_preserved(mocker, session):
    """
    SourceConversationWrapper contains ReplyBoxWidget - this tests that we do not recreate
    SourceConversationWrapper when we click away from a given source. We should create it the
    first time, and then it should persist.
    """
    mv = MainView(None)
    mv.set_conversation = mocker.MagicMock()
    source_selected = mocker.patch("securedrop_client.gui.widgets.SourceList.source_selected")
    mv.controller = mocker.MagicMock(is_authenticated=True)
    source = factory.Source()
    source2 = factory.Source()
    session.add(source)
    session.add(source2)
    session.commit()

    source_conversation_init = mocker.patch(
        "securedrop_client.gui.widgets.SourceConversationWrapper.__init__", return_value=None
    )

    # We expect on the first call, SourceConversationWrapper.__init__ should be called.
    mocker.patch(
        "securedrop_client.gui.widgets.SourceList.get_selected_source", return_value=source
    )
    mv.on_source_changed()
    assert mv.set_conversation.call_count == 1
    assert source_conversation_init.call_count == 1
    source_selected.emit.assert_called_once_with(source.uuid)

    # Reset mocked objects for the next call of on_source_changed.
    source_conversation_init.reset_mock()
    mv.set_conversation.reset_mock()
    source_selected.reset_mock()

    # Now click on another source (source2). Since this is the first time we have clicked
    # on source2, we expect on the first call, SourceConversationWrapper.__init__ should be
    # called.
    mocker.patch(
        "securedrop_client.gui.widgets.SourceList.get_selected_source", return_value=source2
    )
    mv.on_source_changed()
    assert mv.set_conversation.call_count == 1
    assert source_conversation_init.call_count == 1
    source_selected.emit.assert_called_once_with(source2.uuid)

    # Reset mocked objects for the next call of on_source_changed.
    source_conversation_init.reset_mock()
    mv.set_conversation.reset_mock()
    source_selected.reset_mock()

    # But if we click back (call on_source_changed again) to the source,
    # its SourceConversationWrapper should _not_ be recreated.
    mocker.patch(
        "securedrop_client.gui.widgets.SourceList.get_selected_source", return_value=source
    )
    conversation_wrapper = mv.source_conversations[source.uuid]
    conversation_wrapper.conversation_view = mocker.MagicMock()
    conversation_wrapper.conversation_view.update_conversation = mocker.MagicMock()

    mv.on_source_changed()

    assert mv.set_conversation.call_count == 1

    # Conversation should be redrawn even for existing source (bug #467).
    assert conversation_wrapper.conversation_view.update_conversation.call_count == 1
    assert source_conversation_init.call_count == 0
    source_selected.emit.assert_called_once_with(source.uuid)


def test_MainView_refresh_source_conversations(homedir, mocker, qtbot, session_maker, session):
    """
    Ensure SourceConversationWrappers are updated properly.
    """
    source1 = factory.Source(uuid="rsc-123")
    session.add(source1)

    source2 = factory.Source(uuid="rsc-456")
    session.add(source2)

    session.commit()

    sources = [source1, source2]

    mv = MainView(None)

    mock_gui = mocker.MagicMock()
    controller = logic.Controller("http://localhost", mock_gui, session_maker, homedir, None)
    controller.api = mocker.MagicMock()

    mv.setup(controller)
    mv.source_list.update(sources)
    mv.show()

    # get the conversations created
    mocker.patch(
        "securedrop_client.gui.widgets.SourceList.get_selected_source", return_value=source1
    )
    mv.on_source_changed()

    mocker.patch(
        "securedrop_client.gui.widgets.SourceList.get_selected_source", return_value=source2
    )
    mv.on_source_changed()

    assert len(mv.source_conversations) == 2

    # refresh with no source selected
    mocker.patch("securedrop_client.gui.widgets.SourceList.get_selected_source", return_value=None)
    mv.refresh_source_conversations()

    # refresh with source1 selected while its conversation is being deleted
    mocker.patch(
        "securedrop_client.gui.widgets.SourceList.get_selected_source", return_value=source1
    )
    mv.on_source_changed()

    assert len(mv.source_list.source_items) == 2

    scw1 = mv.source_conversations[source1.uuid]
    sw1 = mv.source_list.get_source_widget(source1.uuid)

    assert mv.isVisible()
    assert scw1.isVisible()
    assert not scw1.conversation_title_bar.isHidden()
    assert not scw1.reply_box.isHidden()
    assert not scw1.reply_box.text_edit.isEnabled()
    assert not scw1.reply_box.text_edit.placeholder.isHidden()
    assert not scw1.conversation_view.isHidden()
    assert scw1.deletion_indicator.isHidden()
    assert scw1.conversation_deletion_indicator.isHidden()
    assert sw1.deletion_indicator.isHidden()

    controller.delete_conversation(source1)

    assert mv.isVisible()
    assert scw1.isVisible()
    assert not scw1.conversation_title_bar.isHidden()

    assert not scw1.reply_box.isHidden()
    assert not scw1.reply_box.text_edit.isEnabled()
    assert not scw1.reply_box.text_edit.placeholder.isHidden()

    assert scw1.conversation_view.isHidden()
    assert scw1.deletion_indicator.isHidden()
    assert not scw1.conversation_deletion_indicator.isHidden()
    assert not sw1.deletion_indicator.isHidden()

    # ensure that a refresh does not hide the deletion animation since the success or failure
    # signals should be the only way to stop/hide the animation
    mv.refresh_source_conversations()
    assert not scw1.conversation_deletion_indicator.isHidden()

    scw1.on_source_deleted(source1.uuid)
    assert not scw1.deletion_indicator.isHidden()
    assert scw1.conversation_deletion_indicator.isHidden()


def test_MainView_refresh_source_conversations_with_deleted(
    homedir, mocker, session, session_maker
):
    mv = MainView(None)

    mock_gui = mocker.MagicMock()
    controller = logic.Controller("http://localhost", mock_gui, session_maker, homedir, None)
    controller.api = mocker.MagicMock()

    debug_logger = mocker.patch("securedrop_client.gui.widgets.logger.debug")
    mv.setup(controller)

    source1 = factory.Source(uuid="rsc-123")
    session.add(source1)

    source2 = factory.Source(uuid="rsc-456")
    session.add(source2)

    session.commit()

    sources = [source1, source2]

    mv.source_list.update(sources)
    mv.show()

    def collection_error():
        raise sqlalchemy.exc.InvalidRequestError()

    mocker.patch(
        "securedrop_client.gui.widgets.SourceList.get_selected_source", return_value=source1
    )
    mv.on_source_changed()

    mock_collection = mocker.patch(
        "securedrop_client.db.Source.collection", new_callable=PropertyMock
    )
    ire = sqlalchemy.exc.InvalidRequestError()
    mock_collection.side_effect = ire
    mv.refresh_source_conversations()
    debug_logger.assert_any_call("Error refreshing source conversations: %s", ire)


def test_MainView_set_conversation(mocker):
    """
    Ensure the passed-in widget is added to the layout of the main view holder
    (i.e. that area of the screen on the right hand side).
    """
    mv = MainView(None)
    mv.view_layout = mocker.MagicMock()

    mock_widget = mocker.MagicMock()
    mv.set_conversation(mock_widget)

    mv.view_layout.takeAt.assert_called_once_with(0)
    mv.view_layout.addWidget.assert_called_once_with(mock_widget)


def test_EmptyConversationView_show_no_sources_message(mocker):
    ecv = EmptyConversationView()

    ecv.show_no_sources_message()

    assert not ecv.no_sources.isHidden()
    assert ecv.no_source_selected.isHidden()


def test_EmptyConversationView_show_no_source_selected_message(mocker):
    ecv = EmptyConversationView()

    ecv.show_no_source_selected_message()

    assert ecv.no_sources.isHidden()
    assert not ecv.no_source_selected.isHidden()


def test_SourceList_get_selected_source(mocker):
    """
    Maintains the selected item if present in new list
    """
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    sources = [factory.Source(), factory.Source()]
    sl.update(sources)

    assert sl.get_selected_source() is None

    sl.setCurrentItem(sl.itemAt(1, 0))  # select source2

    current_source = sl.get_selected_source()

    assert current_source.id == sources[1].id


def test_SourceList_update_adds_new_sources(mocker):
    """
    Check a new SourceWidget for each passed-in source is created and no widgets are cleared or
    removed.
    """
    sl = SourceList()

    sl.clear = mocker.MagicMock()
    sl.insertItem = mocker.MagicMock()
    sl.takeItem = mocker.MagicMock()
    sl.setItemWidget = mocker.MagicMock()
    sl.controller = mocker.MagicMock()
    sl.setCurrentItem = mocker.MagicMock()

    mock_sw = mocker.MagicMock()
    mock_lwi = mocker.MagicMock()
    mocker.patch("securedrop_client.gui.widgets.SourceWidget", mock_sw)
    mocker.patch("securedrop_client.gui.widgets.SourceListWidgetItem", mock_lwi)

    sources = [mocker.MagicMock(), mocker.MagicMock(), mocker.MagicMock()]
    sl.update(sources)

    assert mock_sw.call_count == len(sources)
    assert mock_lwi.call_count == len(sources)
    assert sl.insertItem.call_count == len(sources)
    assert sl.setItemWidget.call_count == len(sources)
    assert len(sl.source_items) == len(sources)
    assert sl.setCurrentItem.call_count == 0
    sl.clear.assert_not_called()
    sl.takeItem.assert_not_called()
    mock_sw.deleteLater.assert_not_called()


def test_SourceList_initial_update_adds_new_sources(mocker):
    """
    Check a new SourceWidget for each passed-in source is created and no widgets are cleared or
    removed.
    """
    sl = SourceList()

    sl.clear = mocker.MagicMock()
    sl.add_source = mocker.MagicMock()
    sl.setItemWidget = mocker.MagicMock()
    sl.currentRow = mocker.MagicMock(return_value=0)
    sl.item = mocker.MagicMock()
    sl.item().isSelected.return_value = True
    sources = [mocker.MagicMock(), mocker.MagicMock(), mocker.MagicMock()]
    sl.initial_update(sources)
    sl.add_source.assert_called_once_with(sources)


def test_SourceList_update_when_source_deleted(mocker, session, session_maker, homedir):
    """
    Test that SourceWidget.update gracefully continues when source is deleted during an update.

    When SourceList.update calls SourceWidget.update and that SourceWidget's source has been
    deleted by another ongoing sync, then SourceList.update should silently continue since the
    ongoing sync will handle the deletion of the source's widgets.
    """
    mock_gui = mocker.MagicMock()
    controller = logic.Controller("http://localhost", mock_gui, session_maker, homedir, None)

    # create the source in another session
    source = factory.Source()
    session.add(source)
    session.commit()

    # construct the SourceWidget with the source fetched in its
    # controller's session
    oss = controller.session.query(db.Source).filter_by(id=source.id).one()

    # add it to the SourceList
    sl = SourceList()
    sl.setup(controller)
    deleted_uuids = sl.update([oss])
    assert not deleted_uuids
    assert len(sl.source_items) == 1

    # now delete it to simulate what happens during a sync
    session.delete(source)
    session.commit()

    # now verify that updating does not raise an exception, and that the SourceWidget still exists
    # since the sync will end up calling update again and delete it
    deleted_uuids = sl.update([source])
    assert len(deleted_uuids) == 0
    assert not deleted_uuids
    assert len(sl.source_items) == 1

    # finish sync simulation where a local source is deleted
    deleted_uuids = sl.update([])
    assert len(deleted_uuids) == 1
    assert source.uuid in deleted_uuids
    assert len(sl.source_items) == 0


def test_SourceList_add_source_starts_timer(mocker, session_maker, homedir):
    """
    When the add_source method is called it schedules the addition of a source
    to the source list via a single-shot QTimer.
    """
    sl = SourceList()
    sources = [mocker.MagicMock(), mocker.MagicMock(), mocker.MagicMock()]
    mock_timer = mocker.MagicMock()
    mocker.patch("securedrop_client.gui.widgets.QTimer", mock_timer)
    sl.add_source(sources)
    assert mock_timer.singleShot.call_count == 1


class DeletedSource(Mock):
    @property
    def uuid(self):
        raise sqlalchemy.exc.InvalidRequestError()

    @property
    def collection(self):
        raise sqlalchemy.exc.InvalidRequestError()


def test_SourceList_initial_update_does_not_raise_exc_and_no_widget_created(mocker, qtbot):
    """
    This is a regression test to make sure we raise an exception when adding a new source **before**
    we add a SourceWidget to the SourceList and try to insert into the source_items map.
    """
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    mark_seen_signal = mocker.MagicMock()
    # Make sure SourceWidget constructor doesn't raise
    source_widget = SourceWidget(
        sl.controller, factory.Source(), mark_seen_signal, mocker.MagicMock()
    )
    mocker.patch("securedrop_client.gui.widgets.SourceWidget", return_value=source_widget)
    source = DeletedSource()
    sl.initial_update([source])

    def assert_no_source_widget_exists():
        assert sl.count() == 0
        assert len(sl.source_items) == 0

    qtbot.waitUntil(assert_no_source_widget_exists, timeout=2)


def test_SourceList_update_does_not_raise_exc(mocker):
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    source = DeletedSource()
    sl.update([source])


def test_SourceList_update_does_not_raise_exc_when_itemWidget_is_none(mocker):
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    source = factory.Source()
    sl.update([source])  # first add the source so that the next time the same source is updated

    sl.itemWidget = mocker.MagicMock(return_value=None)
    sl.update([source])  # does not raise exception


def test_SourceList_update_maintains_selection(mocker):
    """
    Maintains the selected item if present in new list
    """
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    sources = [factory.Source(), factory.Source()]
    sl.update(sources)

    sl.setCurrentItem(sl.itemAt(0, 0))  # select the first source
    sl.update(sources)

    assert sl.currentItem()
    assert sl.itemWidget(sl.currentItem()).source.id == sources[0].id

    sl.setCurrentItem(sl.itemAt(1, 0))  # select the second source
    sl.update(sources)

    assert sl.currentItem()
    assert sl.itemWidget(sl.currentItem()).source.id == sources[1].id


def test_SourceList_update_with_pre_selected_source_maintains_selection(mocker):
    """
    Check that an existing source widget that is selected remains selected.
    """
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    sl.update([factory.Source(), factory.Source()])
    second_item = sl.itemAt(1, 0)
    sl.setCurrentItem(second_item)  # select the second source
    mocker.patch.object(second_item, "isSelected", return_value=True)

    sl.update([factory.Source(), factory.Source()])

    assert second_item.isSelected() is True


def test_SourceList_update_removes_selected_item_results_in_no_current_selection(mocker):
    """
    Check that no items are currently selected if the currently selected item is deleted.
    """
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    sl.update([factory.Source(uuid="new"), factory.Source(uuid="newer")])

    sl.setCurrentItem(sl.itemAt(0, 0))  # select source with uuid='newer'
    sl.update([factory.Source(uuid="new")])  # delete source with uuid='newer'

    assert not sl.currentItem()


def test_SourceList_update_removes_item_from_end_of_list(mocker):
    """
    Check that the item is removed from the source list and dict if the source no longer exists.
    """
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    sl.update(
        [factory.Source(uuid="new"), factory.Source(uuid="newer"), factory.Source(uuid="newest")]
    )
    assert sl.count() == 3
    sl.update([factory.Source(uuid="newer"), factory.Source(uuid="newest")])
    assert sl.count() == 2
    assert sl.itemWidget(sl.item(0)).source.uuid == "newest"
    assert sl.itemWidget(sl.item(1)).source.uuid == "newer"
    assert len(sl.source_items) == 2


def test_SourceList_update_removes_item_from_middle_of_list(mocker):
    """
    Check that the item is removed from the source list and dict if the source no longer exists.
    """
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    sl.update(
        [factory.Source(uuid="new"), factory.Source(uuid="newer"), factory.Source(uuid="newest")]
    )
    assert sl.count() == 3
    sl.update([factory.Source(uuid="new"), factory.Source(uuid="newest")])
    assert sl.count() == 2
    assert sl.itemWidget(sl.item(0)).source.uuid == "newest"
    assert sl.itemWidget(sl.item(1)).source.uuid == "new"
    assert len(sl.source_items) == 2


def test_SourceList_update_removes_item_from_beginning_of_list(mocker):
    """
    Check that the item is removed from the source list and dict if the source no longer exists.
    """
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    sl.update(
        [factory.Source(uuid="new"), factory.Source(uuid="newer"), factory.Source(uuid="newest")]
    )
    assert sl.count() == 3
    sl.update([factory.Source(uuid="new"), factory.Source(uuid="newer")])
    assert sl.count() == 2
    assert sl.itemWidget(sl.item(0)).source.uuid == "newer"
    assert sl.itemWidget(sl.item(1)).source.uuid == "new"
    assert len(sl.source_items) == 2


def test_SourceList_add_source_closure_adds_sources(mocker):
    """
    The closure (function created within the add_source function) behaves in
    the expected way given the context of the call to add_source.
    """
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    sl.insertItem = mocker.MagicMock()
    sl.setItemWidget = mocker.MagicMock()
    sl.setCurrentItem = mocker.MagicMock()

    mock_sw = mocker.MagicMock()
    mock_lwi = mocker.MagicMock()
    mocker.patch("securedrop_client.gui.widgets.SourceWidget", mock_sw)
    mocker.patch("securedrop_client.gui.widgets.SourceListWidgetItem", mock_lwi)
    sources = [mocker.MagicMock(), mocker.MagicMock(), mocker.MagicMock()]
    mock_timer = mocker.MagicMock()
    mocker.patch("securedrop_client.gui.widgets.QTimer", mock_timer)
    sl.add_source(sources, 1)
    # Now grab the function created within add_source:
    inner_fn = mock_timer.singleShot.call_args_list[0][0][1]
    # Ensure add_source is mocked to avoid recursion in the test and so we
    # can spy on how it's called.
    sl.add_source = mocker.MagicMock()
    # Call the inner function (as if the timer had completed).
    inner_fn()
    assert mock_sw.call_count == 1
    assert mock_lwi.call_count == 1
    assert sl.insertItem.call_count == 1
    assert sl.setItemWidget.call_count == 1
    assert len(sl.source_items) == 1
    assert sl.setCurrentItem.call_count == 0
    sl.add_source.assert_called_once_with(sources[1:], 2)


def test_SourceList_add_source_closure_exits_on_no_more_sources(mocker):
    """
    The closure (function created within the add_source function) behaves in
    the expected way given the context of the call to add_source.
    """
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    sl.addItem = mocker.MagicMock()
    sl.setItemWidget = mocker.MagicMock()
    sl.setCurrentItem = mocker.MagicMock()

    mock_sw = mocker.MagicMock()
    mock_lwi = mocker.MagicMock()
    mocker.patch("securedrop_client.gui.widgets.SourceWidget", mock_sw)
    mocker.patch("securedrop_client.gui.widgets.SourceListWidgetItem", mock_lwi)
    sources = []
    mock_timer = mocker.MagicMock()
    mocker.patch("securedrop_client.gui.widgets.QTimer", mock_timer)
    sl.add_source(sources, 1)
    # Now grab the function created within add_source:
    inner_fn = mock_timer.singleShot.call_args_list[0][0][1]
    # Ensure add_source is mocked to avoid recursion in the test and so we
    # can spy on how it's called.
    sl.add_source = mocker.MagicMock()
    # Call the inner function (as if the timer had completed).
    assert inner_fn() is None
    assert mock_sw.call_count == 0
    assert mock_lwi.call_count == 0
    assert sl.addItem.call_count == 0
    assert sl.setItemWidget.call_count == 0
    assert len(sl.source_items) == 0
    assert sl.setCurrentItem.call_count == 0
    assert sl.add_source.call_count == 0


def test_SourceList_set_snippet(mocker):
    """
    Handle the emitted event in the expected manner.
    """
    sl = SourceList()
    mark_seen_signal = mocker.MagicMock()
    source_widget = SourceWidget(
        mocker.MagicMock(), factory.Source(uuid="mock_uuid"), mark_seen_signal, mocker.MagicMock()
    )
    source_widget.set_snippet = mocker.MagicMock()
    source_item = SourceListWidgetItem(sl)
    sl.setItemWidget(source_item, source_widget)
    sl.source_items = {"mock_uuid": source_item}

    sl.set_snippet("mock_uuid", "msg_uuid", "msg_content")

    source_widget.set_snippet.assert_called_once_with("mock_uuid", "msg_uuid", "msg_content")


def test_SourceList_get_source_widget(mocker):
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    sl.update([factory.Source(uuid="mock_uuid")])
    sl.source_items = {}

    source_widget = sl.get_source_widget("mock_uuid")

    assert source_widget.source_uuid == "mock_uuid"
    assert source_widget == sl.itemWidget(sl.item(0))


def test_SourceList_get_source_widget_does_not_exist(mocker):
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    mock_source = factory.Source(uuid="mock_uuid")
    sl.update([mock_source])
    sl.source_items = {}

    source_widget = sl.get_source_widget("uuid_for_source_not_in_list")

    assert source_widget is None


def test_SourceList_get_source_widget_if_one_exists_in_cache(mocker):
    sl = SourceList()
    mark_seen_signal = mocker.MagicMock()
    source_widget = SourceWidget(
        mocker.MagicMock(), factory.Source(uuid="mock_uuid"), mark_seen_signal, mocker.MagicMock()
    )
    source_item = SourceListWidgetItem(sl)
    sl.setItemWidget(source_item, source_widget)
    sl.source_items["mock_uuid"] = source_item

    assert sl.get_source_widget("mock_uuid") == source_widget


def test_SourceWidget_init_for_seen_source(mocker, session):
    """
    The source widget is properly initialised with the supplied seen source.
    """
    controller = mocker.MagicMock()
    controller.authenticated_user = factory.User(id=1)
    controller.mark_seen = mocker.MagicMock()
    source = factory.Source()

    seen_file = factory.File(source=source)
    seen_message = factory.Message(source=source)
    seen_reply = factory.Reply(source=source)
    session.add(seen_file)
    session.add(seen_message)
    session.add(seen_reply)

    seen_file_for_another_user = factory.File(source=source)
    seen_message_for_another_user = factory.Message(source=source)
    seen_reply_for_another_user = factory.Reply(source=source)
    session.add(seen_file_for_another_user)
    session.add(seen_message_for_another_user)
    session.add(seen_reply_for_another_user)

    draft_reply_from_current_user = factory.DraftReply(
        source=source, journalist_id=controller.authenticated_user.id
    )
    draft_reply_from_another_user = factory.DraftReply(source=source, journalist_id=666)
    session.add(draft_reply_from_current_user)
    session.add(draft_reply_from_another_user)

    session.commit()

    session.add(db.SeenFile(file_id=seen_file.id, journalist_id=controller.authenticated_user.id))
    session.add(
        db.SeenMessage(message_id=seen_message.id, journalist_id=controller.authenticated_user.id)
    )
    session.add(
        db.SeenReply(reply_id=seen_reply.id, journalist_id=controller.authenticated_user.id)
    )
    session.add(db.SeenFile(file_id=seen_file_for_another_user.id, journalist_id=666))
    session.add(db.SeenMessage(message_id=seen_message_for_another_user.id, journalist_id=666))
    session.add(db.SeenReply(reply_id=seen_reply_for_another_user.id, journalist_id=666))

    session.commit()

    sw = SourceWidget(controller, source, mocker.MagicMock(), mocker.MagicMock())

    assert sw.source == source
    assert sw.seen


def test_SourceWidget_init_for_seen_source_with_legacy_data(mocker, session):
    """
    The source widget is properly initialised with the supplied seen source. The source has files,
    messages, and replies with seen records as well as without seen records, where just the is_read
    boolean is set to test legacy data as well.
    """
    controller = mocker.MagicMock()
    controller.authenticated_user = factory.User(id=1)
    controller.mark_seen = mocker.MagicMock()
    source = factory.Source()

    seen_file = factory.File(source=source)
    seen_file_legacy_is_read = factory.File(source=source, is_read=1)
    seen_message = factory.Message(source=source)
    seen_message_legacy_is_read = factory.Message(source=source, is_read=1)
    seen_reply = factory.Reply(source=source)
    session.add(seen_file)
    session.add(seen_file_legacy_is_read)
    session.add(seen_message)
    session.add(seen_message_legacy_is_read)
    session.add(seen_reply)

    seen_file_for_another_user = factory.File(source=source)
    seen_file_for_another_user_legacy_is_read = factory.File(source=source, is_read=1)
    seen_message_for_another_user = factory.Message(source=source)
    seen_message_for_another_user_legacy_is_read = factory.File(source=source, is_read=1)
    seen_reply_for_another_user = factory.Reply(source=source)
    session.add(seen_file_for_another_user)
    session.add(seen_file_for_another_user_legacy_is_read)
    session.add(seen_message_for_another_user)
    session.add(seen_message_for_another_user_legacy_is_read)
    session.add(seen_reply_for_another_user)

    draft_reply_from_current_user = factory.DraftReply(
        source=source, journalist_id=controller.authenticated_user.id
    )
    draft_reply_from_another_user = factory.DraftReply(source=source, journalist_id=666)
    session.add(draft_reply_from_current_user)
    session.add(draft_reply_from_another_user)

    session.commit()

    session.add(db.SeenFile(file_id=seen_file.id, journalist_id=controller.authenticated_user.id))
    session.add(
        db.SeenMessage(message_id=seen_message.id, journalist_id=controller.authenticated_user.id)
    )
    session.add(
        db.SeenReply(reply_id=seen_reply.id, journalist_id=controller.authenticated_user.id)
    )
    session.add(db.SeenFile(file_id=seen_file_for_another_user.id, journalist_id=666))
    session.add(db.SeenMessage(message_id=seen_message_for_another_user.id, journalist_id=666))
    session.add(db.SeenReply(reply_id=seen_reply_for_another_user.id, journalist_id=666))

    session.commit()

    sw = SourceWidget(controller, source, mocker.MagicMock(), mocker.MagicMock())

    assert sw.source == source
    assert sw.seen


def test_SourceWidget_init_for_seen_source_legacy_only(mocker, session):
    """
    The source widget is properly initialised with the supplied seen source. The source has files
    and messages without seen records where just the is_read boolean is set to test legacy data.
    """
    controller = mocker.MagicMock()
    controller.authenticated_user = factory.User(id=1)
    controller.mark_seen = mocker.MagicMock()
    source = factory.Source()

    seen_file = factory.File(source=source, is_read=1)
    seen_message = factory.Message(source=source, is_read=1)
    seen_reply = factory.Reply(source=source)
    session.add(seen_file)
    session.add(seen_message)
    session.add(seen_reply)

    seen_file_for_another_user = factory.File(source=source, is_read=1)
    seen_message_for_another_user = factory.Message(source=source, is_read=1)
    seen_reply_for_another_user = factory.Reply(source=source)
    session.add(seen_file_for_another_user)
    session.add(seen_message_for_another_user)
    session.add(seen_reply_for_another_user)

    draft_reply_from_current_user = factory.DraftReply(
        source=source, journalist_id=controller.authenticated_user.id
    )
    draft_reply_from_another_user = factory.DraftReply(source=source, journalist_id=666)
    session.add(draft_reply_from_current_user)
    session.add(draft_reply_from_another_user)

    session.commit()

    sw = SourceWidget(controller, source, mocker.MagicMock(), mocker.MagicMock())

    assert sw.source == source
    assert sw.source.seen
    assert sw.seen


def test_SourceWidget_init_for_unseen_source(mocker, session):
    """
    The source widget is properly initialised with the supplied unseen source. The source has some
    files and messages with seen records set and some without.
    """
    controller = mocker.MagicMock()
    controller.authenticated_user = factory.User(id=1)
    controller.mark_seen = mocker.MagicMock()
    source = factory.Source()

    seen_file = factory.File(source=source)
    seen_message = factory.Message(source=source)
    seen_reply = factory.Reply(source=source)
    session.add(seen_file)
    session.add(seen_message)
    session.add(seen_reply)

    seen_file_for_another_user = factory.File(source=source)
    seen_message_for_another_user = factory.Message(source=source)
    seen_reply_for_another_user = factory.Reply(source=source)
    session.add(seen_file_for_another_user)
    session.add(seen_message_for_another_user)
    session.add(seen_reply_for_another_user)

    unseen_file = factory.File(source=source)
    unseen_message = factory.Message(source=source)
    unseen_reply = factory.Reply(source=source)
    session.add(unseen_file)
    session.add(unseen_message)
    session.add(unseen_reply)

    draft_reply_from_current_user = factory.DraftReply(
        source=source, journalist_id=controller.authenticated_user.id
    )
    draft_reply_from_another_user = factory.DraftReply(source=source, journalist_id=666)
    session.add(draft_reply_from_current_user)
    session.add(draft_reply_from_another_user)

    session.commit()

    session.add(db.SeenFile(file_id=seen_file.id, journalist_id=controller.authenticated_user.id))
    session.add(
        db.SeenMessage(message_id=seen_message.id, journalist_id=controller.authenticated_user.id)
    )
    session.add(
        db.SeenReply(reply_id=seen_reply.id, journalist_id=controller.authenticated_user.id)
    )
    session.add(db.SeenFile(file_id=seen_file_for_another_user.id, journalist_id=666))
    session.add(db.SeenMessage(message_id=seen_message_for_another_user.id, journalist_id=666))
    session.add(db.SeenReply(reply_id=seen_reply_for_another_user.id, journalist_id=666))

    session.commit()

    sw = SourceWidget(controller, source, mocker.MagicMock(), mocker.MagicMock())

    assert sw.source == source
    assert not sw.seen


def test_SourceWidget_init_for_unseen_source_legacy_only(mocker, session):
    """
    The source widget is properly initialised with the supplied unseen source. The source has some
    files and messages with is_read set and some without.
    """
    controller = mocker.MagicMock()
    controller.authenticated_user = factory.User(id=1)
    controller.mark_seen = mocker.MagicMock()
    source = factory.Source()

    seen_file = factory.File(source=source, is_read=1)
    seen_message = factory.Message(source=source, is_read=1)
    seen_reply = factory.Reply(source=source)
    session.add(seen_file)
    session.add(seen_message)
    session.add(seen_reply)

    seen_file_for_another_user = factory.File(source=source, is_read=1)
    seen_message_for_another_user = factory.Message(source=source, is_read=1)
    seen_reply_for_another_user = factory.Reply(source=source)
    session.add(seen_file_for_another_user)
    session.add(seen_message_for_another_user)
    session.add(seen_reply_for_another_user)

    unseen_file = factory.File(source=source)
    unseen_message = factory.Message(source=source)
    unseen_reply = factory.Reply(source=source)
    session.add(unseen_file)
    session.add(unseen_message)
    session.add(unseen_reply)

    draft_reply_from_current_user = factory.DraftReply(
        source=source, journalist_id=controller.authenticated_user.id
    )
    draft_reply_from_another_user = factory.DraftReply(source=source, journalist_id=666)
    session.add(draft_reply_from_current_user)
    session.add(draft_reply_from_another_user)

    session.commit()

    sw = SourceWidget(controller, source, mocker.MagicMock(), mocker.MagicMock())

    assert sw.source == source
    assert not sw.seen


def test_SourceWidget_html_init(mocker):
    """
    The source widget is initialised with the given source name, with
    HTML escaped properly.
    """
    controller = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    mock_source.journalist_designation = "foo <b>bar</b> baz"
    mark_seen_signal = mocker.MagicMock()

    sw = SourceWidget(controller, mock_source, mark_seen_signal, mocker.MagicMock())
    sw.name = mocker.MagicMock()
    sw.summary_layout = mocker.MagicMock()

    mocker.patch("securedrop_client.gui.base.SvgLabel")
    sw.update()

    sw.name.setText.assert_called_once_with("foo <b>bar</b> baz")


def test_SourceWidget__on_adjust_preview(mocker):
    """
    Ensure width of the source widget is set to the width passed into adjust_preview.
    """
    sl = SourceList()
    sw = SourceWidget(mocker.MagicMock(), factory.Source(), mocker.MagicMock(), mocker.MagicMock())
    sw.preview = mocker.MagicMock()
    source_item = SourceListWidgetItem(sl)
    sl.setItemWidget(source_item, sw)

    sw._on_adjust_preview(100)

    assert sw.width() == 100
    sw.preview.adjust_preview.assert_called_with(100)


def test_SourceList_resizeEvent(mocker):
    sl = SourceList()
    sl.adjust_preview = mocker.MagicMock()
    sl.resizeEvent(QResizeEvent(QSize(100, 100), QSize(100, 100)))
    sl.adjust_preview.emit.assert_called_once_with(100)


def test_SourcePreview_adjust_preview(mocker):
    preview = SourcePreview()
    preview.refresh_preview_text = mocker.MagicMock()
    preview.adjust_preview(400)
    preview.refresh_preview_text.assert_called_once_with()
    assert preview.max_length == 400 - preview.PREVIEW_WIDTH_DIFFERENCE
    assert preview.width() == 400 - preview.PREVIEW_WIDTH_DIFFERENCE


def test_SourceWidget_update_styles_to_read(mocker):
    """
    Ensure styles are updated so that the source widget appears read when seen is True.
    """
    sw = SourceWidget(mocker.MagicMock(), factory.Source(), mocker.MagicMock(), mocker.MagicMock())
    sw.seen = True
    name = mocker.patch.object(sw, "name")
    timestamp = mocker.patch.object(sw, "timestamp")
    preview = mocker.patch.object(sw, "preview")

    sw.update_styles()

    name.setObjectName.assert_called_with("SourceWidget_name")
    timestamp.setObjectName.assert_called_with("SourceWidget_timestamp")
    preview.setObjectName.assert_called_with("SourceWidget_preview")


def test_SourceWidget_update_styles_to_read_selected(mocker):
    """
    Ensure styles are updated so that the source widget appears read and selected when seen and
    selected are True.
    """
    sw = SourceWidget(mocker.MagicMock(), factory.Source(), mocker.MagicMock(), mocker.MagicMock())
    sw.seen = True
    sw.selected = True
    name = mocker.patch.object(sw, "name")
    timestamp = mocker.patch.object(sw, "timestamp")
    preview = mocker.patch.object(sw, "preview")

    sw.update_styles()

    name.setObjectName.assert_called_with("SourceWidget_name_selected")
    timestamp.setObjectName.assert_called_with("SourceWidget_timestamp")
    preview.setObjectName.assert_called_with("SourceWidget_preview")


def test_test_SourceWidget_update_styles_to_unread(mocker):
    """
    Ensure styles are updated so that the source widget appears unread when seen is False.
    """
    sw = SourceWidget(mocker.MagicMock(), factory.Source(), mocker.MagicMock(), mocker.MagicMock())
    sw.seen = False
    name = mocker.patch.object(sw, "name")
    timestamp = mocker.patch.object(sw, "timestamp")
    preview = mocker.patch.object(sw, "preview")

    sw.update_styles()

    name.setObjectName.assert_called_with("SourceWidget_name_unread")
    timestamp.setObjectName.assert_called_with("SourceWidget_timestamp_unread")
    preview.setObjectName.assert_called_with("SourceWidget_preview_unread")


def test_SourceWidget__on_authentication_changed(mocker):
    """
    Ensure that:

    * The source widget always displays as having been seen if user is offline.
    * The source widget's seen status remains unchanged when the authentication status changes
      to the user being online. (Seen status will be corrected in `SourceWidget.update`.)
    """
    sw = SourceWidget(mocker.MagicMock(), factory.Source(), mocker.MagicMock(), mocker.MagicMock())
    sw.seen = False
    sw.update_styles = mocker.MagicMock()

    sw._on_authentication_changed(authenticated=False)

    sw.update_styles.assert_called_once_with()
    assert sw.seen
    sw._on_authentication_changed(authenticated=False)
    assert sw.seen
    sw._on_authentication_changed(authenticated=True)
    assert sw.seen
    sw.seen = False
    sw._on_authentication_changed(authenticated=True)
    assert not sw.seen


def test_SourceWidget__on_source_selected(mocker, session):
    """
    Ensure the source widget is selected and seen status updates to True when it's selected.
    """
    controller = mocker.MagicMock()
    controller.authenticated_user = factory.User(id=1)
    source = factory.Source()
    sw = SourceWidget(controller, source, mocker.MagicMock(), mocker.MagicMock())
    sw.seen = False
    sw.update_styles = mocker.MagicMock()

    sw._on_source_selected(source.uuid)

    assert sw.seen
    assert sw.selected
    sw.update_styles.assert_called_once_with()


def test_SourceWidget__on_source_selected_skips_op_if_uuid_does_not_match(mocker):
    """
    Ensure the source widget is not selected and seen status remains the same if uuid does not match
    the selected source.
    """
    controller = mocker.MagicMock()
    source = factory.Source()
    sw = SourceWidget(controller, source, mocker.MagicMock(), mocker.MagicMock())
    sw.seen = False
    sw.update_styles = mocker.MagicMock()

    sw._on_source_selected("some-other-uuid")

    assert not sw.seen
    assert not sw.selected
    sw.update_styles.assert_called_with()


def test_SourceWidget__on_source_selected_skips_op_if_already_seen(mocker):
    controller = mocker.MagicMock()
    source = factory.Source()
    sw = SourceWidget(controller, source, mocker.MagicMock(), mocker.MagicMock())
    sw.seen = True
    sw.update_styles = mocker.MagicMock()

    sw._on_source_selected(source.uuid)

    sw.seen = True
    sw.update_styles.assert_called_once_with()


def test_SourceWidget__on_sync_started(mocker):
    sw = SourceWidget(mocker.MagicMock(), factory.Source(), mocker.MagicMock(), mocker.MagicMock())
    timestamp = datetime.now()
    sw._on_sync_started(timestamp)
    assert sw.sync_started_timestamp == timestamp


def test_SourceWidget__on_conversation_deletion_successful(mocker):
    sw = SourceWidget(mocker.MagicMock(), factory.Source(), mocker.MagicMock(), mocker.MagicMock())
    timestamp = datetime.now()
    sw._on_conversation_deletion_successful(sw.source.uuid, timestamp)
    assert sw.deletion_scheduled_timestamp == timestamp
    assert sw.preview.text() == "\u2014 All files and messages deleted for this source \u2014"
    assert sw.deleting_conversation is False
    assert sw.deletion_indicator.isHidden()


def test_SourceWidget_update_attachment_icon(mocker):
    """
    Attachment icon identicates document count
    """
    controller = mocker.MagicMock()
    source = factory.Source(document_count=1)
    mark_seen_signal = mocker.MagicMock()
    sw = SourceWidget(controller, source, mark_seen_signal, mocker.MagicMock())

    sw.update()
    assert not sw.paperclip.isHidden()

    source.document_count = 0

    sw.update()
    assert sw.paperclip.isHidden()


def test_SourceWidget_update_does_not_raise_exception(mocker):
    """
    If the source no longer exists in the local data store, ensure the SourceWidget just logs and
    does not raise an exception.
    """
    controller = mocker.MagicMock()
    source = factory.Source(document_count=1)
    mark_seen_signal = mocker.MagicMock()
    sw = SourceWidget(controller, source, mark_seen_signal, mocker.MagicMock())
    ex = sqlalchemy.exc.InvalidRequestError()
    controller.session.refresh.side_effect = ex
    mock_logger = mocker.MagicMock()
    mocker.patch("securedrop_client.gui.widgets.logger", mock_logger)
    sw.update()
    assert mock_logger.debug.call_count == 1


def test_SourceWidget_update_skips_setting_snippet_if_deletion_in_progress(mocker):
    """
    If the source is being deleted, do not update the snippet.
    """
    sw = SourceWidget(mocker.MagicMock(), factory.Source(), mocker.MagicMock(), mocker.MagicMock())
    sw.deleting = True
    sw.set_snippet = mocker.MagicMock()
    sw.update()
    sw.set_snippet.assert_not_called()


def test_SourceWidget_update_skips_setting_snippet_if_sync_is_stale(mocker):
    """
    If the sync started before the source was scheduled for deletion, do not update the snippet.
    """
    sw = SourceWidget(mocker.MagicMock(), factory.Source(), mocker.MagicMock(), mocker.MagicMock())
    sw.sync_started_timestamp = datetime.now()
    sw.deletion_scheduled_timestamp = datetime.now()
    sw.set_snippet = mocker.MagicMock()
    sw.update()
    sw.set_snippet.assert_not_called()


def test_SourceWidget_update_skips_setting_snippet_if_conversation_deletion_in_progress(mocker):
    """
    If the source conversation is being deleted, do not update the snippet.
    """
    sw = SourceWidget(mocker.MagicMock(), factory.Source(), mocker.MagicMock(), mocker.MagicMock())
    sw.deleting_conversation = True
    sw.set_snippet = mocker.MagicMock()
    sw.update()
    sw.set_snippet.assert_not_called()


def test_SourceWidget_set_snippet_draft_only(mocker, session_maker, session, homedir):
    """
    Snippets/previews do not include draft messages.
    """
    mock_gui = mocker.MagicMock()
    controller = logic.Controller("http://localhost", mock_gui, session_maker, homedir, None)
    source = factory.Source(document_count=1)
    mark_seen_signal = mocker.MagicMock()
    f = factory.File(source=source)
    reply = factory.DraftReply(source=source)
    session.add(f)
    session.add(source)
    session.add(reply)
    session.commit()

    sw = SourceWidget(controller, source, mark_seen_signal, mocker.MagicMock())
    sw.set_snippet(source.uuid, reply.uuid, f.filename)
    assert sw.preview.text() == "File: " + f.filename


def test_SourceWidget_set_snippet(mocker, session_maker, session, homedir):
    """
    Snippets are set as expected.
    """
    mock_gui = mocker.MagicMock()
    controller = logic.Controller("http://localhost", mock_gui, session_maker, homedir, None)
    source = factory.Source(document_count=1)
    mark_seen_signal = mocker.MagicMock()
    f = factory.File(source=source)
    session.add(f)
    session.add(source)
    session.commit()

    sw = SourceWidget(controller, source, mark_seen_signal, mocker.MagicMock())
    sw.set_snippet(source.uuid, "mock_file_uuid", f.filename)
    assert sw.preview.text() == "File: " + f.filename

    # check when a different source is specified
    sw.set_snippet("not-the-source-uuid", "mock_file_uuid", "something new")
    assert sw.preview.text() == "File: " + f.filename

    source_uuid = source.uuid
    session.delete(source)
    session.commit()

    # check when the source has been deleted that it catches sqlalchemy.exc.InvalidRequestError
    sw.set_snippet(source_uuid, "mock_file_uuid", "something new")


def test_SourceWidget_update_truncate_latest_msg(mocker):
    """
    If the latest message in the conversation is longer than 150 characters,
    truncate and add "..." to the end.
    """
    controller = mocker.MagicMock()
    source = mocker.MagicMock()
    source.journalist_designation = "Testy McTestface"
    source.collection = [factory.Message(content="a" * 151)]
    source.server_collection = source.collection
    mark_seen_signal = mocker.MagicMock()
    sw = SourceWidget(controller, source, mark_seen_signal, mocker.MagicMock())

    sw.update()
    assert sw.preview.text().endswith("...")


def test_SourceWidget__on_source_deleted(mocker, session, source):
    controller = mocker.MagicMock()
    mark_seen_signal = mocker.MagicMock()
    sw = SourceWidget(controller, factory.Source(uuid="123"), mark_seen_signal, mocker.MagicMock())
    sw._on_source_deleted("123")
    assert sw.star.isHidden()
    assert not sw.name.isHidden()
    assert sw.paperclip.isHidden()
    assert sw.preview.isHidden()
    assert not sw.timestamp.isHidden()
    assert not sw.deletion_indicator.isHidden()
    assert sw.preview.text() == ""

    # simulate set_snippet after the source is deleted but before sync
    sw.set_snippet("123")
    assert sw.preview.text() == ""


def test_SourceWidget__on_source_deleted_wrong_uuid(mocker, session, source):
    controller = mocker.MagicMock()
    mark_seen_signal = mocker.MagicMock()
    source = factory.Source(uuid="123")
    source.document_count = mocker.MagicMock(return_value=1)
    sw = SourceWidget(controller, source, mark_seen_signal, mocker.MagicMock())
    sw._on_source_deleted("321")
    assert not sw.star.isHidden()
    assert not sw.name.isHidden()
    assert not sw.paperclip.isHidden()
    assert not sw.preview.isHidden()
    assert sw.deletion_indicator.isHidden()
    assert not sw.timestamp.isHidden()


def test_SourceWidget__on_source_deletion_failed(mocker, session, source):
    controller = mocker.MagicMock()
    mark_seen_signal = mocker.MagicMock()
    sw = SourceWidget(controller, factory.Source(uuid="123"), mark_seen_signal, mocker.MagicMock())
    sw._on_source_deleted("123")

    sw._on_source_deletion_failed("123")

    assert not sw.star.isHidden()
    assert not sw.name.isHidden()
    assert sw.paperclip.isHidden()
    assert not sw.preview.isHidden()
    assert sw.deletion_indicator.isHidden()
    assert not sw.timestamp.isHidden()


def test_SourceWidget__on_source_deletion_failed_wrong_uuid(mocker, session, source):
    controller = mocker.MagicMock()
    mark_seen_signal = mocker.MagicMock()
    sw = SourceWidget(controller, factory.Source(uuid="123"), mark_seen_signal, mocker.MagicMock())
    sw._on_source_deleted("123")

    sw._on_source_deletion_failed("321")

    assert sw.star.isHidden()
    assert not sw.name.isHidden()
    assert sw.paperclip.isHidden()
    assert sw.preview.isHidden()
    assert not sw.deletion_indicator.isHidden()
    assert not sw.timestamp.isHidden()


def test_SourceWidget__on_source_conversation_deleted_with_empty_collection(
    mocker, session, source
):
    controller = mocker.MagicMock()
    mark_seen_signal = mocker.MagicMock()

    source = factory.Source()
    session.add(source)
    session.commit()

    sw = SourceWidget(controller, source, mark_seen_signal, mocker.MagicMock())
    sw._on_conversation_deleted(source.uuid)
    assert not sw.star.isHidden()
    assert not sw.name.isHidden()
    assert not sw.timestamp.isHidden()
    # with an empty collection, all paperclips are hidden
    assert sw.paperclip.isHidden()
    assert sw.paperclip_disabled.isHidden()
    assert sw.preview.isHidden()
    assert not sw.deletion_indicator.isHidden()


def test_SourceWidget__on_source_conversation_deleted_with_document(mocker, session):
    controller = mocker.MagicMock()

    source = factory.Source()
    session.add(source)

    doc = factory.File(source=source)
    session.add(doc)
    source.document_count = len(source.files)
    session.commit()

    assert source.document_count == 1

    sw = SourceWidget(controller, source, mocker.MagicMock(), mocker.MagicMock())
    sw._on_conversation_deleted(source.uuid)
    assert not sw.star.isHidden()
    assert not sw.name.isHidden()
    assert not sw.timestamp.isHidden()
    # with a collection, the paperclip is shown during deletion, but disabled
    assert sw.paperclip.isHidden()
    assert not sw.paperclip_disabled.isHidden()
    assert sw.preview.isHidden()
    assert not sw.deletion_indicator.isHidden()


def test_SourceWidget_preview_after_conversation_deleted(mocker, session, i18n):
    # a source with non-zero interaction count, but zero submissions,
    # has had its conversation deleted
    source = factory.Source()
    session.add(source)
    source.interaction_count = 3
    session.commit()

    controller = mocker.MagicMock()
    sw = SourceWidget(controller, source, mocker.MagicMock(), mocker.MagicMock())
    sw.update()
    assert sw.preview.property("class") == "conversation_deleted"
    assert sw.preview.text() == _("\u2014 All files and messages deleted for this source \u2014")


def test_SourceWidget__on_source_conversation_deleted_wrong_uuid(mocker, session, source):
    controller = mocker.MagicMock()
    mark_seen_signal = mocker.MagicMock()
    source = factory.Source(uuid="123")
    source.document_count = mocker.MagicMock(return_value=1)
    sw = SourceWidget(controller, source, mark_seen_signal, mocker.MagicMock())
    sw._on_conversation_deleted("321")
    assert not sw.star.isHidden()
    assert not sw.name.isHidden()
    assert not sw.paperclip.isHidden()
    assert not sw.preview.isHidden()
    assert sw.deletion_indicator.isHidden()
    assert not sw.timestamp.isHidden()


def test_SourceWidget__on_source_conversation_deletion_failed(mocker, session, source):
    controller = mocker.MagicMock()
    mark_seen_signal = mocker.MagicMock()
    sw = SourceWidget(controller, factory.Source(uuid="123"), mark_seen_signal, mocker.MagicMock())
    sw._on_conversation_deleted("123")

    sw._on_conversation_deletion_failed("123")

    assert not sw.star.isHidden()
    assert not sw.name.isHidden()
    assert sw.paperclip.isHidden()
    assert not sw.preview.isHidden()
    assert sw.deletion_indicator.isHidden()
    assert not sw.timestamp.isHidden()


def test_SourceWidget__on_source_conversation_deletion_failed_wrong_uuid(mocker, session, source):
    controller = mocker.MagicMock()
    mark_seen_signal = mocker.MagicMock()
    sw = SourceWidget(controller, factory.Source(uuid="123"), mark_seen_signal, mocker.MagicMock())
    sw._on_conversation_deleted("123")

    sw._on_conversation_deletion_failed("321")

    assert not sw.star.isHidden()
    assert not sw.name.isHidden()
    assert sw.paperclip.isHidden()
    assert sw.preview.isHidden()
    assert not sw.deletion_indicator.isHidden()
    assert not sw.timestamp.isHidden()


def test_SourceWidget_uses_SecureQLabel(mocker):
    """
    Ensure the source widget preview uses SecureQLabel and is not injectable
    """
    controller = mocker.MagicMock()
    source = mocker.MagicMock()
    source.journalist_designation = "Testy McTestface"
    source.collection = [factory.Message(content="a" * 121)]
    mark_seen_signal = mocker.MagicMock()
    sw = SourceWidget(controller, source, mark_seen_signal, mocker.MagicMock())

    sw.update()
    assert isinstance(sw.preview, SecureQLabel)

    sw.preview.setTextFormat = mocker.MagicMock()
    sw.preview.setText("<b>bad text</b>")
    sw.update()
    sw.preview.setTextFormat.assert_called_with(Qt.PlainText)


def test_StarToggleButton_init_source_starred(mocker):
    controller = mocker.MagicMock()
    source = factory.Source(is_starred=True)

    stb = StarToggleButton(controller, source.uuid, source.is_starred)

    assert stb.source_uuid == source.uuid
    assert stb.isChecked() is True


def test_StarToggleButton_init_source_unstarred(mocker):
    controller = mocker.MagicMock()
    source = factory.Source(is_starred=False)

    stb = StarToggleButton(controller, source.uuid, source.is_starred)

    assert stb.source_uuid == source.uuid
    assert stb.isChecked() is False


def test_StarToggleButton_eventFilter_when_checked(mocker):
    """
    Ensure the hover events are handled properly when star is checked and online.
    """
    controller = mocker.MagicMock()
    controller.is_authenticated = True
    stb = StarToggleButton(controller, "mock_uuid", True)
    stb.pressed = mocker.MagicMock()
    stb.setIcon = mocker.MagicMock()
    stb.set_icon = mocker.MagicMock()
    load_icon_fn = mocker.patch("securedrop_client.gui.widgets.load_icon")

    # Hover enter
    test_event = QEvent(QEvent.HoverEnter)
    stb.eventFilter(stb, test_event)
    assert stb.setIcon.call_count == 1
    load_icon_fn.assert_called_once_with("star_hover.svg")

    # Hover leave
    test_event = QEvent(QEvent.HoverLeave)
    stb.eventFilter(stb, test_event)
    stb.set_icon.assert_called_once_with(on="star_on.svg", off="star_off.svg")

    # Authentication change
    stb.on_authentication_changed(True)
    assert stb.isCheckable() is True
    stb.pressed.disconnect.assert_called_once_with()
    stb.pressed.connect.assert_called_once_with(stb.on_pressed)


def test_StarToggleButton_eventFilter_when_not_checked(mocker):
    """
    Ensure the hover events are handled properly when star is checked and online.
    """
    controller = mocker.MagicMock()
    controller.is_authenticated = True
    stb = StarToggleButton(controller, "mock_uuid", False)
    stb.pressed = mocker.MagicMock()
    stb.setIcon = mocker.MagicMock()
    stb.set_icon = mocker.MagicMock()
    load_icon_fn = mocker.patch("securedrop_client.gui.widgets.load_icon")

    # Hover enter
    test_event = QEvent(QEvent.HoverEnter)
    stb.eventFilter(stb, test_event)
    assert stb.setIcon.call_count == 1
    load_icon_fn.assert_called_once_with("star_hover.svg")

    # Hover leave
    test_event = QEvent(QEvent.HoverLeave)
    stb.eventFilter(stb, test_event)
    stb.set_icon.assert_called_once_with(on="star_on.svg", off="star_off.svg")

    # Authentication change
    stb.on_authentication_changed(True)
    assert stb.isCheckable() is True
    stb.pressed.disconnect.assert_called_once_with()
    stb.pressed.connect.assert_called_once_with(stb.on_pressed)


def test_StarToggleButton_eventFilter_when_checked_and_offline(mocker):
    """
    Ensure the hover events do not change the icon when offline and that the star icon is set to
    off='star_on.svg' when checked and offline.
    """
    controller = mocker.MagicMock()
    stb = StarToggleButton(controller, "mock_uuid", True)
    stb.pressed = mocker.MagicMock()
    stb.setIcon = mocker.MagicMock()
    stb.set_icon = mocker.MagicMock()
    load_icon_fn = mocker.patch("securedrop_client.gui.widgets.load_icon")

    # Authentication change
    stb.on_authentication_changed(False)
    assert stb.isCheckable() is False
    stb.set_icon.assert_called_with(on="star_on.svg", off="star_on.svg")
    stb.pressed.disconnect.assert_called_once_with()
    stb.pressed.connect.assert_called_once_with(stb.on_pressed_offline)

    # Hover enter
    test_event = QEvent(QEvent.HoverEnter)
    stb.eventFilter(stb, test_event)
    stb.setIcon.assert_not_called()
    load_icon_fn.assert_not_called()

    # Hover leave
    test_event = QEvent(QEvent.HoverLeave)
    stb.eventFilter(stb, test_event)
    stb.setIcon.assert_not_called()


def test_StarToggleButton_eventFilter_when_not_checked_and_offline(mocker):
    """
    Ensure the hover events do not change the icon when offline and that the star icon is set to
    off='star_on.svg' when unchecked and offline.
    """
    controller = mocker.MagicMock()
    stb = StarToggleButton(controller, "mock_uuid", False)
    stb.pressed = mocker.MagicMock()
    stb.setIcon = mocker.MagicMock()
    stb.set_icon = mocker.MagicMock()
    load_icon_fn = mocker.patch("securedrop_client.gui.widgets.load_icon")

    # Authentication change
    stb.on_authentication_changed(False)
    assert stb.isCheckable() is False
    stb.pressed.disconnect.assert_called_once_with()
    stb.pressed.connect.assert_called_once_with(stb.on_pressed_offline)

    # Hover enter
    test_event = QEvent(QEvent.HoverEnter)
    stb.eventFilter(stb, test_event)
    stb.setIcon.assert_not_called()
    load_icon_fn.assert_not_called()

    # Hover leave
    test_event = QEvent(QEvent.HoverLeave)
    stb.eventFilter(stb, test_event)
    stb.setIcon.assert_not_called()


def test_StarToggleButton_on_authentication_changed_while_authenticated_and_checked(mocker):
    """
    If on_authentication_changed is set up correctly, then toggling a checked button should result
    in the button being unchecked.
    """
    controller = mocker.MagicMock()
    stb = StarToggleButton(controller, "mock_uuid", True)
    stb.on_pressed = mocker.MagicMock()
    stb.on_authentication_changed(True)

    stb.click()

    stb.on_pressed.assert_called_once_with()
    assert stb.isChecked() is False


def test_StarToggleButton_on_authentication_changed_while_authenticated_and_not_checked(mocker):
    """
    If on_authentication_changed is set up correctly, then calling toggle on an unchecked button
    should result in the button being unchecked.
    """
    controller = mocker.MagicMock()
    stb = StarToggleButton(controller, "mock_uuid", False)
    stb.on_pressed = mocker.MagicMock()
    stb.on_authentication_changed(True)

    stb.click()

    stb.on_pressed.assert_called_once_with()
    assert stb.isChecked() is True


def test_StarToggleButton_on_authentication_changed_while_offline_mode_and_not_checked(mocker):
    """
    Ensure on_authentication_changed is set up correctly for offline mode.
    """
    controller = mocker.MagicMock()
    stb = StarToggleButton(controller, "mock_uuid", False)
    stb.on_pressed_offline = mocker.MagicMock()
    stb.on_pressed = mocker.MagicMock()
    stb.on_authentication_changed(False)

    stb.click()

    stb.on_pressed_offline.assert_called_once_with()
    stb.on_pressed.assert_not_called()
    assert stb.isChecked() is False


def test_StarToggleButton_on_authentication_changed_while_offline_mode_and_checked(mocker):
    """
    Ensure on_authentication_changed is set up correctly for offline mode.
    """
    controller = mocker.MagicMock()
    stb = StarToggleButton(controller, "mock_uuid", True)
    stb.on_pressed_offline = mocker.MagicMock()
    stb.on_pressed = mocker.MagicMock()
    stb.on_authentication_changed(False)

    stb.click()

    stb.on_pressed_offline.assert_called_once_with()
    stb.on_pressed.assert_not_called()
    assert stb.isCheckable() is False
    assert stb.is_starred is True


def test_StarToggleButton_on_pressed_toggles_to_starred(mocker):
    """
    Ensure pressing the star button toggles from unstarred to starred.
    """
    controller = mocker.MagicMock()
    stb = StarToggleButton(controller, "mock_uuid", False)

    stb.click()

    stb.controller.update_star.assert_called_once_with("mock_uuid", False)
    assert stb.isChecked()


def test_StarToggleButton_on_pressed_toggles_to_unstarred(mocker):
    """
    Ensure pressing the star button toggles from starred to unstarred.
    """
    controller = mocker.MagicMock()
    stb = StarToggleButton(controller, "mock_uuid", True)

    stb.click()

    stb.controller.update_star.assert_called_once_with("mock_uuid", True)
    assert not stb.isChecked()


def test_StarToggleButton_on_pressed_offline(mocker):
    """
    Ensure toggle is disabled when offline.
    """
    controller = mocker.MagicMock()
    controller.is_authenticated = False
    stb = StarToggleButton(controller, "mock_uuid", True)

    stb.click()

    stb.controller.on_action_requiring_login.assert_called_once_with()


def test_StarToggleButton_on_pressed_offline_when_checked(mocker):
    """
    Ensure correct star icon images are loaded for the disabled button.
    """
    controller = mocker.MagicMock()
    controller.is_authenticated = False
    source = factory.Source(is_starred=True)
    stb = StarToggleButton(controller, source.uuid, source.is_starred)
    set_icon_fn = mocker.patch("securedrop_client.gui.base.SvgToggleButton.set_icon")

    stb.on_authentication_changed(False)
    assert stb.isCheckable() is False
    set_icon_fn.assert_called_with(on="star_on.svg", off="star_on.svg")

    stb.click()
    stb.controller.on_action_requiring_login.assert_called_once_with()


def test_StarToggleButton_update(mocker):
    """
    Ensure update syncs the star state with the server if there are no pending jobs and we're not
    waiting until the next sync (in order to avoid the "ghost" issue where update is called with an
    outdated state between a star job finishing and a sync).
    """
    controller = mocker.MagicMock()
    controller.is_authenticated = True
    stb = StarToggleButton(controller, "mock_uuid", True)

    # Should not change because we wait until next sync
    stb.pending_count = 0
    stb.wait_until_next_sync = True
    stb.update(False)
    assert stb.isChecked() is True
    stb.update(True)
    assert stb.isChecked() is True

    # Should update to match value provided by update because there are no pending star jobs and
    # wait_until_next_sync is False, meaning a sync already occurred after the star job finished
    stb.setChecked(True)
    stb.pending_count = 0
    stb.wait_until_next_sync = False
    stb.update(False)
    assert stb.isChecked() is False
    stb.update(True)
    assert stb.isChecked() is True

    # Should not change because there are pending star jobs
    stb.setChecked(True)
    stb.pending_count = 1
    stb.wait_until_next_sync = True
    stb.update(False)
    assert stb.isChecked() is True
    stb.update(True)
    assert stb.isChecked() is True
    # Still should not change because there are pending star jobs
    stb.wait_until_next_sync = False
    stb.update(False)
    assert stb.isChecked() is True
    stb.update(True)
    assert stb.isChecked() is True


def test_StarToggleButton_update_when_not_authenticated(mocker):
    """
    Ensure the button state does not change if the user is not authenticated.
    """
    controller = mocker.MagicMock()
    controller.is_authenticated = False
    source = factory.Source(is_starred=True)
    stb = StarToggleButton(controller, source.uuid, source.is_starred)

    # Button stays checked
    stb.update(False)
    assert stb.is_starred is True

    # Button stays unchecked
    stb.is_starred = False
    stb.update(True)
    assert stb.is_starred is False


def test_StarToggleButton_on_star_update_failed(mocker):
    """
    Ensure the button is toggled to the state provided in the failure handler and that the pending
    count is decremented if the source uuid matches.
    """
    controller = mocker.MagicMock()
    controller.is_authenticated = True
    stb = StarToggleButton(controller, "mock_uuid", False)

    stb.click()
    assert stb.is_starred is True
    assert stb.pending_count == 1
    stb.on_star_update_failed("mock_uuid", is_starred=False)
    assert stb.is_starred is False
    assert stb.pending_count == 0


def test_StarToggleButton_on_star_update_failed_for_non_matching_source_uuid(mocker):
    """
    Ensure the button is not toggled and that the pending count stays the same if the source uuid
    does not match.
    """
    controller = mocker.MagicMock()
    controller.is_authenticated = True
    stb = StarToggleButton(controller, "mock_uuid", False)

    stb.click()
    assert stb.is_starred is True
    assert stb.pending_count == 1
    stb.on_star_update_failed("some_other_uuid", is_starred=False)
    assert stb.is_starred is True
    assert stb.pending_count == 1


def test_StarToggleButton_on_star_update_successful(mocker):
    """
    Ensure that the pending count is decremented if the source uuid matches.
    """
    controller = mocker.MagicMock()
    controller.is_authenticated = True
    stb = StarToggleButton(controller, "mock_uuid", True)

    stb.click()
    assert stb.pending_count == 1
    stb.on_star_update_successful("mock_uuid")
    assert stb.pending_count == 0


def test_StarToggleButton_on_star_update_successful_for_non_matching_source_uuid(mocker):
    """
    Ensure that the pending count is not decremented if the source uuid does not match.
    """
    controller = mocker.MagicMock()
    controller.is_authenticated = True
    stb = StarToggleButton(controller, "mock_uuid", True)

    stb.click()
    assert stb.pending_count == 1
    stb.on_star_update_successful("some_other_uuid")
    assert stb.pending_count == 1


def test_SpeechBubble_init(mocker):
    """
    Check the speech bubble is configured correctly with supplied message text.
    """
    mock_update_signal = mocker.Mock()
    mock_update_connect = mocker.Mock()
    mock_update_signal.connect = mock_update_connect

    mock_download_error_signal = mocker.Mock()
    mock_download_error_connect = mocker.Mock()
    mock_download_error_signal.connect = mock_download_error_connect

    sb = SpeechBubble("mock id", "hello", mock_update_signal, mock_download_error_signal, 0, 123)

    sb.message.text() == "hello"

    assert mock_update_connect.called
    assert mock_download_error_connect.called


def test_SpeechBubble_init_with_error(mocker):
    """
    Check the speech bubble is configured correctly when failed_to_decrypt=True.
    """
    mock_update_signal = mocker.Mock()
    mock_update_connect = mocker.Mock()
    mock_update_signal.connect = mock_update_connect

    mock_download_error_signal = mocker.Mock()
    mock_download_error_connect = mocker.Mock()
    mock_download_error_signal.connect = mock_download_error_connect

    sb = SpeechBubble(
        "mock id",
        "hello",
        mock_update_signal,
        mock_download_error_signal,
        0,
        SpeechBubble.MIN_CONTAINER_WIDTH,
        failed_to_decrypt=True,
    )

    sb.message.text() == "hello"
    assert mock_update_connect.called
    assert mock_download_error_connect.called


def test_SpeechBubble_adjust_width(mocker):
    """
    Ensure that the speech bubble is set to the minimum allowed width if the supplied container
    width is smaller than the minimum allowed container width. Otherwise check that the width
    is set to the width of the container multiplied by the stretch factor ratio.
    """

    sb = SpeechBubble(
        "mock id", "hello", mocker.Mock(), mocker.Mock(), 0, SpeechBubble.MIN_CONTAINER_WIDTH
    )

    sb.adjust_width(sb.MIN_CONTAINER_WIDTH - 1)
    assert sb.speech_bubble.width() == sb.MIN_WIDTH

    sb.adjust_width(sb.MIN_CONTAINER_WIDTH)
    assert sb.speech_bubble.width() == math.floor(
        sb.MIN_CONTAINER_WIDTH * sb.WIDTH_TO_CONTAINER_WIDTH_RATIO
    )


def test_SpeechBubble_update_text(mocker):
    """
    Check that the calling the slot updates the text.
    """
    mock_signal = mocker.MagicMock()

    msg_id = "abc123"
    sb = SpeechBubble(
        msg_id, "hello", mock_signal, mock_signal, 0, SpeechBubble.MIN_CONTAINER_WIDTH
    )

    new_msg = "new message"
    sb._update_text("mock_source_uuid", msg_id, new_msg)
    assert sb.message.text() == new_msg

    newer_msg = "an even newer message"
    sb._update_text("mock_source_uuid", msg_id + "xxxxx", newer_msg)
    assert sb.message.text() == new_msg


def test_SpeechBubble_html_init(mocker):
    """
    Check the speech bubble is configured correctly (there's a label containing
    the passed in text, with HTML escaped properly).
    """
    mock_signal = mocker.MagicMock()
    bubble = SpeechBubble(
        "mock id", "<b>hello</b>", mock_signal, mock_signal, 0, SpeechBubble.MIN_CONTAINER_WIDTH
    )
    assert bubble.message.text() == "<b>hello</b>"


def test_SpeechBubble_with_apostrophe_in_text(mocker):
    """Check Speech Bubble is displaying text with apostrophe correctly."""
    mock_signal = mocker.MagicMock()

    message = "I'm sure, you are reading my message."
    bubble = SpeechBubble(
        "mock id", message, mock_signal, mock_signal, 0, SpeechBubble.MIN_CONTAINER_WIDTH
    )
    assert bubble.message.text() == message


def test_SpeechBubble__on_download_error(mocker):
    mock_signal = mocker.MagicMock()

    message_uuid = "mock id"
    message = "I'm sure, you are reading my message."
    bubble = SpeechBubble(
        message_uuid, message, mock_signal, mock_signal, 0, SpeechBubble.MIN_CONTAINER_WIDTH
    )
    assert bubble.message.text() == message

    error_message = "Oh no."
    bubble._on_download_error("source id", message_uuid, error_message)
    assert bubble.message.text() == error_message


def test_CheckMark_eventFilter_hover(mocker):
    mock_signal = mocker.MagicMock()
    bubble = SpeechBubble(
        "mock id", "<b>hello</b>", mock_signal, mock_signal, 0, SpeechBubble.MIN_CONTAINER_WIDTH
    )

    bubble.check_mark = mocker.MagicMock()

    # Hover enter
    test_event = QEvent(QEvent.HoverEnter)
    bubble.eventFilter(bubble, test_event)
    assert bubble.check_mark.setIcon.call_count
    bubble.check_mark.setIcon.reset_mock()  # ensure that it is the exact svg file we want

    # Hover leave
    test_event = QEvent(QEvent.HoverLeave)
    bubble.eventFilter(bubble, test_event)
    assert bubble.check_mark.setIcon.call_count == 1
    bubble.check_mark.setIcon.reset_mock()


def test_SpeechBubble_on_update_authenticated_user(mocker):
    mock_update_signal = mocker.Mock()
    mock_update_connect = mocker.Mock()
    mock_update_signal.connect = mock_update_connect

    mock_download_error_signal = mocker.Mock()
    mock_download_error_connect = mocker.Mock()
    mock_download_error_signal.connect = mock_download_error_connect

    authenticated_user = factory.User()

    sb = SpeechBubble("mock id", "hello", mock_update_signal, mock_download_error_signal, 0, 123)

    sb.on_update_authenticated_user(authenticated_user)
    assert sb.authenticated_user == authenticated_user


def test_MessageWidget_init(mocker):
    """
    Check the CSS is set as expected.
    """
    mock_signal = mocker.Mock()
    mock_connected = mocker.Mock()
    mock_signal.connect = mock_connected

    MessageWidget("abc123", "hello", mock_signal, mock_signal, 0, 123)

    assert mock_connected.called


def test_MessageWidget_set_failed_to_decrypt_styles(mocker):
    """
    Check the CSS is set as expected when failed_to_decrypt=True.
    """
    authenticated_user = factory.User()
    message_widget = MessageWidget(
        "abc123",
        "test message",
        mocker.MagicMock(),
        mocker.MagicMock(),
        0,
        123,
        authenticated_user,
        True,
    )

    message_widget.message = mocker.patch.object(message_widget, "message")
    message_widget.color_bar = mocker.patch.object(message_widget, "color_bar")

    message_widget.set_failed_to_decrypt_styles()

    message_widget.message.setObjectName.assert_called_with("SpeechBubble_message_decryption_error")
    message_widget.color_bar.setObjectName.assert_called_with(
        "SpeechBubble_status_bar_decryption_error"
    )


def test_ReplyWidget_init(mocker):
    """
    Check the CSS is set as expected.
    """
    mock_update_signal = mocker.Mock()
    mock_update_connected = mocker.Mock()
    mock_update_signal.connect = mock_update_connected

    mock_download_failure_signal = mocker.MagicMock()
    mock_download_failure_connected = mocker.Mock()
    mock_download_failure_signal.connect = mock_download_failure_connected

    mock_success_signal = mocker.MagicMock()
    mock_success_connected = mocker.Mock()
    mock_success_signal.connect = mock_success_connected

    mock_failure_signal = mocker.MagicMock()
    mock_failure_connected = mocker.Mock()
    mock_failure_signal.connect = mock_failure_connected

    co = mocker.MagicMock(authentication_state=mocker.MagicMock())
    co.update_authenticated_user = mocker.MagicMock()
    co.authentication_state = mocker.MagicMock()
    sender = factory.User()
    rw = ReplyWidget(
        controller=co,
        message_uuid="mock_uuid",
        message="hello",
        reply_status="dummy",
        update_signal=mock_update_signal,
        download_error_signal=mock_download_failure_signal,
        message_succeeded_signal=mock_success_signal,
        message_failed_signal=mock_failure_signal,
        index=0,
        container_width=123,
        sender=sender,
        sender_is_current_user=False,
        failed_to_decrypt=False,
    )

    co.update_authenticated_user.connect.assert_called_once_with(rw._on_update_authenticated_user)
    co.authentication_state.connect.assert_called_once_with(rw._on_authentication_changed)
    assert mock_update_connected.called
    assert mock_success_connected.called
    assert mock_failure_connected.called


def test_ReplyWidget_init_with_failed_to_send_error(mocker):
    """
    Check the CSS is set as expected when failed_to_decrypt=True.
    """
    mock_update_signal = mocker.Mock()
    mock_update_connected = mocker.Mock()
    mock_update_signal.connect = mock_update_connected

    mock_download_failure_signal = mocker.MagicMock()
    mock_download_failure_connected = mocker.Mock()
    mock_download_failure_signal.connect = mock_download_failure_connected

    mock_success_signal = mocker.MagicMock()
    mock_success_connected = mocker.Mock()
    mock_success_signal.connect = mock_success_connected

    mock_failure_signal = mocker.MagicMock()
    mock_failure_connected = mocker.Mock()
    mock_failure_signal.connect = mock_failure_connected

    co = mocker.MagicMock(authentication_state=mocker.MagicMock())
    co.update_authenticated_user = mocker.MagicMock()
    co.authentication_state = mocker.MagicMock()
    sender = factory.User()
    rw = ReplyWidget(
        controller=co,
        message_uuid="mock_uuid",
        message="hello",
        reply_status="dummy",
        update_signal=mock_update_signal,
        download_error_signal=mock_download_failure_signal,
        message_succeeded_signal=mock_success_signal,
        message_failed_signal=mock_failure_signal,
        index=0,
        container_width=123,
        sender=sender,
        sender_is_current_user=False,
        failed_to_decrypt=True,
    )

    co.update_authenticated_user.connect.assert_called_once_with(rw._on_update_authenticated_user)
    co.authentication_state.connect.assert_called_once_with(rw._on_authentication_changed)
    assert mock_update_connected.called
    assert mock_success_connected.called
    assert mock_failure_connected.called


def test_ReplyBoxWidget__on_authentication_changed_updates_badge_when_switched_to_offline(mocker):
    controller = mocker.MagicMock(authenticated_user=None)
    sender = factory.User()
    reply_widget = ReplyWidget(
        controller=controller,
        message_uuid="mock_uuid",
        message="hello",
        reply_status="dummy",
        update_signal=mocker.MagicMock(),
        download_error_signal=mocker.MagicMock(),
        message_succeeded_signal=mocker.MagicMock(),
        message_failed_signal=mocker.MagicMock(),
        index=0,
        container_width=123,
        sender=sender,
        sender_is_current_user=True,
        failed_to_decrypt=False,
    )
    reply_widget._update_styles = mocker.MagicMock()

    reply_widget._on_authentication_changed(False)

    assert not reply_widget.sender_is_current_user
    assert not reply_widget.sender_icon.is_current_user
    reply_widget._update_styles.assert_called_once_with()


def test_ReplyBoxWidget__on_authentication_changed_does_nothing_when_authenticated(mocker):
    authenticated_user = factory.User()
    controller = mocker.MagicMock(authenticated_user=authenticated_user)

    sender = factory.User()
    sender_is_current_user = random.choice([True, False])
    reply_widget = ReplyWidget(
        controller=controller,
        message_uuid="mock_uuid",
        message="hello",
        reply_status="dummy",
        update_signal=mocker.MagicMock(),
        download_error_signal=mocker.MagicMock(),
        message_succeeded_signal=mocker.MagicMock(),
        message_failed_signal=mocker.MagicMock(),
        index=0,
        container_width=123,
        sender=sender,
        sender_is_current_user=sender_is_current_user,
        failed_to_decrypt=False,
    )
    reply_widget._update_styles = mocker.MagicMock()

    reply_widget._on_authentication_changed(True)

    assert reply_widget.sender_is_current_user == sender_is_current_user
    assert reply_widget.sender_icon.is_current_user == sender_is_current_user
    reply_widget._update_styles.assert_not_called()


def test_ReplyWidget__on_update_authenticated_user_does_not_raise_when_sender_deleted(mocker):
    authenticated_user = factory.User()
    controller = mocker.MagicMock(authenticated_user=authenticated_user)

    class DeletedUser(db.User):
        @property
        def uuid(self):
            raise sqlalchemy.orm.exc.ObjectDeletedError(attributes.instance_state(db.User()), None)

        @property
        def initials(self):
            return "ab"

    reply_widget = ReplyWidget(
        controller=controller,
        message_uuid="mock_uuid",
        message="hello",
        reply_status="dummy",
        update_signal=mocker.MagicMock(),
        download_error_signal=mocker.MagicMock(),
        message_succeeded_signal=mocker.MagicMock(),
        message_failed_signal=mocker.MagicMock(),
        index=0,
        container_width=123,
        sender=DeletedUser(),
        sender_is_current_user=False,
        failed_to_decrypt=False,
    )

    # Ensure that this does not handles `ObjectDeletedError` exception by
    reply_widget._on_update_authenticated_user(authenticated_user)


def test_ReplyWidget__on_update_authenticated_user_does_nothing_when_not_sender(mocker):
    authenticated_user = factory.User()
    controller = mocker.MagicMock(authenticated_user=authenticated_user)

    sender = factory.User()
    reply_widget = ReplyWidget(
        controller=controller,
        message_uuid="mock_uuid",
        message="hello",
        reply_status="dummy",
        update_signal=mocker.MagicMock(),
        download_error_signal=mocker.MagicMock(),
        message_succeeded_signal=mocker.MagicMock(),
        message_failed_signal=mocker.MagicMock(),
        index=0,
        container_width=123,
        sender=sender,
        sender_is_current_user=False,
        failed_to_decrypt=False,
    )
    reply_widget._update_styles = mocker.MagicMock()

    reply_widget._on_update_authenticated_user(authenticated_user)

    assert not reply_widget.sender_is_current_user
    assert not reply_widget.sender_icon.is_current_user
    reply_widget._update_styles.assert_not_called()


def test_ReplyWidget__on_update_authenticated_user(mocker):
    authenticated_user = factory.User()
    controller = mocker.MagicMock(authenticated_user=authenticated_user)

    reply_widget = ReplyWidget(
        controller=controller,
        message_uuid="mock_uuid",
        message="hello",
        reply_status="dummy",
        update_signal=mocker.MagicMock(),
        download_error_signal=mocker.MagicMock(),
        message_succeeded_signal=mocker.MagicMock(),
        message_failed_signal=mocker.MagicMock(),
        index=0,
        container_width=123,
        sender=authenticated_user,
        sender_is_current_user=False,
        failed_to_decrypt=False,
    )
    reply_widget._update_styles = mocker.MagicMock()

    reply_widget._on_update_authenticated_user(authenticated_user)

    assert reply_widget.sender_is_current_user
    assert reply_widget.sender_icon.is_current_user
    reply_widget._update_styles.assert_called_once_with()


def test_ReplyWidget__on_update_authenticated_user_updates_sender_when_changed(mocker, homedir):
    authenticated_user = factory.User()
    co = mocker.MagicMock(authenticated_user=authenticated_user)
    co = logic.Controller("http://localhost", mocker.MagicMock(), mocker.MagicMock(), homedir, None)
    user = factory.User(uuid="abc123", username="foo")
    co.authenticated_user = user
    co.session.refresh = mocker.MagicMock()
    co.update_authenticated_user = mocker.MagicMock()

    reply_widget = ReplyWidget(
        controller=co,
        message_uuid="mock_uuid",
        message="hello",
        reply_status="dummy",
        update_signal=mocker.MagicMock(),
        download_error_signal=mocker.MagicMock(),
        message_succeeded_signal=mocker.MagicMock(),
        message_failed_signal=mocker.MagicMock(),
        index=0,
        container_width=123,
        sender=authenticated_user,
        sender_is_current_user=False,
        failed_to_decrypt=False,
    )
    reply_widget._update_styles = mocker.MagicMock()

    user = co.session.query(db.User).filter_by(uuid="abc123").one()
    user.username = "baz"
    reply_widget._on_update_authenticated_user(authenticated_user)

    reply_widget.sender.username == "baz"
    assert reply_widget.sender_is_current_user
    assert reply_widget.sender_icon.is_current_user
    reply_widget._update_styles.assert_called_once_with()


def test_ReplyWidget_sets_pending_status_bar_for_current_user(mocker):
    controller = mocker.MagicMock(authentication_state=mocker.MagicMock())
    sender = factory.User()
    rw = ReplyWidget(
        controller=controller,
        message_uuid="mock_uuid",
        message="hello",
        reply_status="dummy",
        update_signal=mocker.MagicMock(),
        download_error_signal=mocker.MagicMock(),
        message_succeeded_signal=mocker.MagicMock(),
        message_failed_signal=mocker.MagicMock(),
        index=0,
        container_width=123,
        sender=sender,
        sender_is_current_user=True,
        failed_to_decrypt=True,
    )
    rw.color_bar = mocker.MagicMock()

    rw.set_pending_styles()

    rw.color_bar.setObjectName.assert_called_once_with(
        "ReplyWidget_status_bar_pending_current_user"
    )


def test_FileWidget_init_file_not_downloaded(mocker, source, session):
    """
    Check the FileWidget is configured correctly when the file is not downloaded.
    """
    file = factory.File(source=source["source"], is_downloaded=False, is_decrypted=None)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(
        "mock", controller, mocker.MagicMock(), mocker.MagicMock(), mocker.MagicMock(), 0, 123
    )

    assert fw.controller == controller
    assert fw.file.is_downloaded is False
    assert not fw.download_button.isHidden()
    assert not fw.no_file_name.isHidden()
    assert fw.export_button.isHidden()
    assert fw.middot.isHidden()
    assert fw.print_button.isHidden()
    assert fw.file_name.isHidden()


def test_FileWidget_init_file_downloaded(mocker, source, session):
    """
    Check the FileWidget is configured correctly when the file is downloaded.
    """
    file = factory.File(source=source["source"], is_downloaded=True)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(
        "mock", controller, mocker.MagicMock(), mocker.MagicMock(), mocker.MagicMock(), 0, 123
    )

    assert fw.controller == controller
    assert fw.file.is_downloaded is True
    assert fw.download_button.isHidden()
    assert fw.no_file_name.isHidden()
    assert not fw.export_button.isHidden()
    assert not fw.middot.isHidden()
    assert not fw.print_button.isHidden()
    assert not fw.file_name.isHidden()


def test_FileWidget_adjust_width(mocker):
    """
    Ensure that the file widget is set to the minimum allowed width if the supplied container width
    is smaller than the minimum allowed container width. Otherwise check that the width is set
    to the width of the container multiplied by the stretch factor ratio.
    """
    file = factory.File(source=factory.Source(), is_downloaded=True)
    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(
        "abc123-ima-uuid",
        controller,
        mocker.MagicMock(),
        mocker.MagicMock(),
        mocker.MagicMock(),
        0,
        123,
    )

    fw.adjust_width(fw.MIN_CONTAINER_WIDTH - 1)
    assert fw.width() == fw.MIN_WIDTH

    fw.adjust_width(fw.MIN_CONTAINER_WIDTH)
    assert fw.width() == math.floor(fw.MIN_CONTAINER_WIDTH * fw.WIDTH_TO_CONTAINER_WIDTH_RATIO)


def test_FileWidget__set_file_state_under_mouse(mocker, source, session):
    """
    If the download_button is under the mouse, it should show the "hover"
    version of the download_file icon.
    """
    file_ = factory.File(source=source["source"], is_downloaded=False, is_decrypted=None)
    session.add(file_)
    session.commit()

    get_file = mocker.MagicMock(return_value=file_)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(
        file_.uuid,
        controller,
        mocker.MagicMock(),
        mocker.MagicMock(),
        mocker.MagicMock(),
        0,
        123,
    )
    fw.download_button.underMouse = mocker.MagicMock(return_value=True)
    fw.download_button.setIcon = mocker.MagicMock()
    mock_load = mocker.MagicMock()
    mocker.patch("securedrop_client.gui.widgets.load_icon", mock_load)
    fw._set_file_state()
    mock_load.assert_called_once_with("download_file_hover.svg")


def test_FileWidget_event_handler_left_click(mocker, session, source):
    """
    Left click on filename should trigger an open.
    """
    file_ = factory.File(source=source["source"], is_downloaded=False, is_decrypted=None)
    session.add(file_)
    session.commit()

    get_file = mocker.MagicMock(return_value=file_)
    controller = mocker.MagicMock(get_file=get_file)

    test_event = QEvent(QEvent.MouseButtonPress)
    test_event.button = mocker.MagicMock(return_value=Qt.LeftButton)

    fw = FileWidget(
        file_.uuid,
        controller,
        mocker.MagicMock(),
        mocker.MagicMock(),
        mocker.MagicMock(),
        0,
        123,
    )
    fw._on_left_click = mocker.MagicMock()

    fw.eventFilter(fw, test_event)
    fw._on_left_click.call_count == 1


def test_FileWidget_event_handler_hover(mocker, session, source):
    """
    Hover events when the file isn't being downloaded should change the
    widget's icon.
    """
    file_ = factory.File(source=source["source"], is_downloaded=False, is_decrypted=None)
    session.add(file_)
    session.commit()

    get_file = mocker.MagicMock(return_value=file_)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(
        file_.uuid,
        controller,
        mocker.MagicMock(),
        mocker.MagicMock(),
        mocker.MagicMock(),
        0,
        123,
    )
    fw.download_button = mocker.MagicMock()

    # Hover enter
    test_event = QEvent(QEvent.HoverEnter)
    fw.eventFilter(fw, test_event)
    assert fw.download_button.setIcon.call_count == 1
    fw.download_button.setIcon.reset_mock()
    # Hover leave
    test_event = QEvent(QEvent.HoverLeave)
    fw.eventFilter(fw, test_event)
    assert fw.download_button.setIcon.call_count == 1
    fw.download_button.setIcon.reset_mock()


def test_FileWidget_on_left_click_download(mocker, session, source):
    """
    Left click on download when file is not downloaded should trigger
    a download.
    """
    file_ = factory.File(source=source["source"], is_downloaded=False, is_decrypted=None)
    session.add(file_)
    session.commit()

    get_file = mocker.MagicMock(return_value=file_)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(
        file_.uuid,
        controller,
        mocker.MagicMock(),
        mocker.MagicMock(),
        mocker.MagicMock(),
        0,
        123,
    )
    fw.download_button = mocker.MagicMock()
    get_file.assert_called_once_with(file_.uuid)
    get_file.reset_mock()

    fw._on_left_click()
    get_file.assert_called_once_with(file_.uuid)
    controller.on_submission_download.assert_called_once_with(db.File, file_.uuid)


def test_FileWidget_on_left_click_downloading_in_progress(mocker, session, source):
    """
    Left click on download when file is not downloaded but is in progress
    downloading should not trigger a download.
    """
    file_ = factory.File(source=source["source"], is_downloaded=False, is_decrypted=None)
    session.add(file_)
    session.commit()

    get_file = mocker.MagicMock(return_value=file_)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(
        file_.uuid,
        controller,
        mocker.MagicMock(),
        mocker.MagicMock(),
        mocker.MagicMock(),
        0,
        123,
    )
    fw.downloading = True
    fw.download_button = mocker.MagicMock()
    get_file.assert_called_once_with(file_.uuid)
    get_file.reset_mock()

    fw._on_left_click()
    get_file.call_count == 0
    controller.on_submission_download.call_count == 0


def test_FileWidget_start_button_animation(mocker, session, source):
    """
    Ensure widget state is updated when this method is called.
    """
    file_ = factory.File(source=source["source"], is_downloaded=False, is_decrypted=None)
    session.add(file_)
    session.commit()

    get_file = mocker.MagicMock(return_value=file_)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(
        file_.uuid,
        controller,
        mocker.MagicMock(),
        mocker.MagicMock(),
        mocker.MagicMock(),
        0,
        123,
    )
    fw.download_button = mocker.MagicMock()
    fw.start_button_animation()
    # Check indicators of activity have been updated.
    assert fw.download_button.setIcon.call_count == 1


def test_FileWidget_on_left_click_open(mocker, session, source):
    """
    Left click on open when file is downloaded should trigger an open.
    """
    file_ = factory.File(source=source["source"], is_downloaded=True)
    session.add(file_)
    session.commit()

    get_file = mocker.MagicMock(return_value=file_)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(
        file_.uuid,
        controller,
        mocker.MagicMock(),
        mocker.MagicMock(),
        mocker.MagicMock(),
        0,
        123,
    )
    fw._on_left_click()
    fw.controller.on_file_open.assert_called_once_with(file_)


def test_FileWidget_set_button_animation_frame(mocker, session, source):
    """
    Left click on download when file is not downloaded should trigger
    a download.
    """
    file_ = factory.File(source=source["source"], is_downloaded=False, is_decrypted=None)
    session.add(file_)
    session.commit()

    get_file = mocker.MagicMock(return_value=file_)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(
        file_.uuid,
        controller,
        mocker.MagicMock(),
        mocker.MagicMock(),
        mocker.MagicMock(),
        0,
        123,
    )
    fw.download_button = mocker.MagicMock()
    fw.set_button_animation_frame(1)
    assert fw.download_button.setIcon.call_count == 1


def test_FileWidget_update(mocker, session, source):
    """
    The update method should show/hide widgets if file is downloaded
    """
    file = factory.File(source=source["source"], is_downloaded=True)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(
        file.uuid,
        controller,
        mocker.MagicMock(),
        mocker.MagicMock(),
        mocker.MagicMock(),
        0,
        123,
    )

    fw.update()

    assert fw.download_button.isHidden()
    assert fw.no_file_name.isHidden()
    assert not fw.file_name.isHidden()


def test_FileWidget_on_file_download_updates_items_when_uuid_matches(mocker, source, session):
    """
    The _on_file_download method should update the FileWidget
    """
    file = factory.File(source=source["source"], is_downloaded=True)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(
        file.uuid,
        controller,
        mocker.MagicMock(),
        mocker.MagicMock(),
        mocker.MagicMock(),
        0,
        123,
    )
    fw.update = mocker.MagicMock()

    fw._on_file_downloaded(file.source.uuid, file.uuid, str(file))

    assert fw.download_button.isHidden()
    assert not fw.export_button.isHidden()
    assert not fw.middot.isHidden()
    assert not fw.print_button.isHidden()
    assert fw.no_file_name.isHidden()
    assert not fw.file_name.isHidden()


def test_FileWidget_on_file_download_started_updates_items_when_uuid_matches(
    mocker, source, session
):
    """
    The _on_download_started method should update the FileWidget
    """
    file = factory.File(source=source["source"])
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(
        file.uuid,
        controller,
        mocker.MagicMock(),
        mocker.MagicMock(),
        mocker.MagicMock(),
        0,
        123,
    )
    fw.update = mocker.MagicMock()

    assert not fw.downloading

    fw._on_file_download_started(file.uuid)

    assert fw.downloading


def test_FileWidget_filename_truncation(mocker, source, session):
    """
    FileWidget should truncate long filenames.

    The full filename should be available in the tooltip.
    """
    filename = "1-{}".format("x" * 1000)
    file = factory.File(source=source["source"], filename=filename)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(
        file.uuid,
        controller,
        mocker.MagicMock(),
        mocker.MagicMock(),
        mocker.MagicMock(),
        0,
        123,
    )
    fw.update = mocker.MagicMock()

    fw._on_file_downloaded(file.source.uuid, file.uuid, str(file))

    assert fw.file_name.text().endswith("...")
    assert fw.file_name.toolTip() == filename


def test_FileWidget_on_file_download_updates_items_when_uuid_does_not_match(
    mocker, homedir, session, source
):
    """
    The _on_file_download method should clear and update the FileWidget
    """
    file = factory.File(source=source["source"], is_downloaded=True)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(
        file.uuid,
        controller,
        mocker.MagicMock(),
        mocker.MagicMock(),
        mocker.MagicMock(),
        0,
        123,
    )
    fw.clear = mocker.MagicMock()
    fw.update = mocker.MagicMock()

    fw._on_file_downloaded("not a matching source uuid", "not a matching file uuid", "mock")

    fw.clear.assert_not_called()
    assert fw.download_button.isHidden()
    assert not fw.export_button.isHidden()
    assert not fw.middot.isHidden()
    assert not fw.print_button.isHidden()
    assert fw.no_file_name.isHidden()
    assert not fw.file_name.isHidden()


def test_FileWidget_on_file_missing_show_download_button_when_uuid_matches(
    mocker, source, session, session_maker, homedir
):
    """
    The _on_file_missing method should update the FileWidget when uuid matches.
    """
    file = factory.File(source=source["source"], is_decrypted=None, is_downloaded=False)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(
        file.uuid,
        controller,
        controller.file_download_started,
        controller.file_ready,
        controller.file_missing,
        0,
        123,
    )
    fw._on_file_missing(file.source.uuid, file.uuid, str(file))

    # this is necessary for the timer that stops the download
    # animation to execute
    QTest.qWait(1000)

    assert not fw.download_button.isHidden()
    assert fw.export_button.isHidden()
    assert fw.middot.isHidden()
    assert fw.print_button.isHidden()
    assert not fw.no_file_name.isHidden()
    assert fw.file_name.isHidden()
    assert fw.download_animation.state() == QMovie.NotRunning


def test_FileWidget_on_file_missing_does_not_show_download_button_when_uuid_does_not_match(
    mocker, homedir, session, source
):
    """
    The _on_file_missing method should not update the FileWidget when uuid doesn't match.
    """
    file = factory.File(source=source["source"])
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(
        file.uuid,
        controller,
        mocker.MagicMock(),
        mocker.MagicMock(),
        mocker.MagicMock(),
        0,
        123,
    )
    fw.download_button.show = mocker.MagicMock()

    fw._on_file_missing("not a matching source uuid", "not a matching file uuid", "mock filename")

    fw.download_button.show.assert_not_called()


def test_FileWidget__on_export_clicked(mocker, session, source):
    """
    Ensure preflight checks start when the EXPORT button is clicked and that password is requested
    """
    file = factory.File(source=source["source"], is_downloaded=True)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)
    export_device = mocker.patch("securedrop_client.gui.conversation.ExportDevice")

    fw = FileWidget(
        file.uuid, controller, mocker.MagicMock(), mocker.MagicMock(), mocker.MagicMock(), 0, 123
    )
    fw.update = mocker.MagicMock()
    mocker.patch("PyQt5.QtWidgets.QDialog.exec")
    controller.run_export_preflight_checks = mocker.MagicMock()
    controller.downloaded_file_exists = mocker.MagicMock(return_value=True)

    dialog = mocker.patch("securedrop_client.gui.conversation.ExportFileDialog")

    fw._on_export_clicked()
    dialog.assert_called_once_with(export_device(), file.uuid, file.filename)


def test_FileWidget__on_export_clicked_missing_file(mocker, session, source):
    """
    Ensure dialog does not open when the EXPORT button is clicked yet the file to export is missing
    """
    file = factory.File(source=source["source"], is_downloaded=True)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(
        file.uuid,
        controller,
        mocker.MagicMock(),
        mocker.MagicMock(),
        mocker.MagicMock(),
        0,
        123,
    )
    fw.update = mocker.MagicMock()
    mocker.patch("PyQt5.QtWidgets.QDialog.exec")
    controller.run_export_preflight_checks = mocker.MagicMock()
    controller.downloaded_file_exists = mocker.MagicMock(return_value=False)
    dialog = mocker.patch("securedrop_client.gui.conversation.ExportFileDialog")

    fw._on_export_clicked()

    controller.run_export_preflight_checks.assert_not_called()
    dialog.assert_not_called()


def test_FileWidget__on_print_clicked(mocker, session, source):
    """
    Ensure print_file is called when the PRINT button is clicked
    """
    file = factory.File(source=source["source"], is_downloaded=True)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)
    export_device = mocker.patch("securedrop_client.gui.conversation.ExportDevice")

    fw = FileWidget(
        file.uuid,
        controller,
        mocker.MagicMock(),
        mocker.MagicMock(),
        mocker.MagicMock(),
        0,
        123,
    )
    fw.update = mocker.MagicMock()
    mocker.patch("PyQt5.QtWidgets.QDialog.exec")
    controller.print_file = mocker.MagicMock()
    controller.downloaded_file_exists = mocker.MagicMock(return_value=True)

    dialog = mocker.patch("securedrop_client.gui.conversation.PrintFileDialog")

    fw._on_print_clicked()

    dialog.assert_called_once_with(export_device(), file.uuid, file.filename)


def test_FileWidget__on_print_clicked_missing_file(mocker, session, source):
    """
    Ensure dialog does not open when the EXPORT button is clicked yet the file to export is missing
    """
    file = factory.File(source=source["source"], is_downloaded=True)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(
        file.uuid,
        controller,
        mocker.MagicMock(),
        mocker.MagicMock(),
        mocker.MagicMock(),
        0,
        123,
    )
    fw.update = mocker.MagicMock()
    mocker.patch("PyQt5.QtWidgets.QDialog.exec")
    controller.print_file = mocker.MagicMock()
    controller.downloaded_file_exists = mocker.MagicMock(return_value=False)
    dialog = mocker.patch("securedrop_client.gui.conversation.PrintFileDialog")

    fw._on_print_clicked()

    controller.print_file.assert_not_called()
    dialog.assert_not_called()


def test_FileWidget_update_file_size_with_deleted_file(
    mocker, homedir, config, session_maker, source
):
    gui = mocker.MagicMock()
    with threads(3) as [sync_thread, main_queue_thread, file_download_queue_thread]:
        controller = logic.Controller(
            "http://localhost",
            gui,
            session_maker,
            homedir,
            None,
            sync_thread=sync_thread,
            main_queue_thread=main_queue_thread,
            file_download_queue_thread=file_download_queue_thread,
        )

        file = factory.File(source=source["source"], is_downloaded=True)
        controller.session.add(file)
        controller.session.commit()

        fw = FileWidget(
            file.uuid,
            controller,
            mocker.MagicMock(),
            mocker.MagicMock(),
            mocker.MagicMock(),
            0,
            123,
        )

        mocker.patch(
            "securedrop_client.gui.widgets.humanize_filesize", side_effect=Exception("boom!")
        )
        fw.update_file_size()
        assert fw.file_size.text() == ""


def test_SourceConversationWrapper_on_conversation_updated(mocker, qtbot):
    source = factory.Source()
    file = factory.File(source=source, is_downloaded=True)

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    scw = SourceConversationWrapper(source, controller, None)
    scw.conversation_title_bar.updated.setText("CANARY")

    scw.conversation_view.add_file(file=file, index=1)

    expected_timestamp = arrow.get(source.last_updated).format("MMM D")

    def check_timestamp():
        assert scw.conversation_title_bar.updated.text() == expected_timestamp

    qtbot.waitUntil(check_timestamp, timeout=2000)


def test_SourceConversationWrapper_on_source_deleted(mocker):
    source = factory.Source(uuid="123")
    mv = MainView(None)
    mv.source_list = mocker.MagicMock()
    mv.source_list.get_selected_source = mocker.MagicMock(return_value=source)
    mv.controller = mocker.MagicMock(is_authenticated=True)
    mv.show()
    scw = SourceConversationWrapper(source, mv.controller, None)
    mocker.patch("securedrop_client.gui.widgets.SourceConversationWrapper", return_value=scw)
    mv.on_source_changed()
    scw.on_source_deleted("123")

    assert mv.isVisible()
    assert scw.isVisible()
    assert not scw.conversation_title_bar.isHidden()
    assert not scw.reply_box.isHidden()
    assert not scw.reply_box.text_edit.isEnabled()
    assert not scw.reply_box.text_edit.placeholder.isHidden()
    assert scw.reply_box.text_edit.document().isEmpty()
    assert scw.conversation_view.isHidden()
    assert not scw.deletion_indicator.isHidden()


def test_SourceConversationWrapper_on_source_deleted_wrong_uuid(mocker):
    scw = SourceConversationWrapper(factory.Source(uuid="123"), mocker.MagicMock())
    scw.on_source_deleted("321")
    assert not scw.conversation_title_bar.isHidden()
    assert not scw.conversation_view.isHidden()
    assert not scw.reply_box.isHidden()
    assert scw.deletion_indicator.isHidden()


def test_SourceConversationWrapper_on_source_deletion_failed(mocker):
    scw = SourceConversationWrapper(factory.Source(uuid="123"), mocker.MagicMock())
    scw.on_source_deleted("123")

    scw.on_source_deletion_failed("123")

    assert not scw.conversation_title_bar.isHidden()
    assert not scw.conversation_view.isHidden()
    assert not scw.reply_box.isHidden()
    assert scw.deletion_indicator.isHidden()


def test_SourceConversationWrapper_on_source_deletion_failed_wrong_uuid(mocker):
    scw = SourceConversationWrapper(factory.Source(uuid="123"), mocker.MagicMock())
    scw.on_source_deleted("123")

    scw.on_source_deletion_failed("321")

    assert not scw.conversation_title_bar.isHidden()
    assert scw.conversation_view.isHidden()
    assert not scw.reply_box.isHidden()
    assert not scw.deletion_indicator.isHidden()


def test_SourceConversationWrapper_on_conversation_deleted(mocker):
    source = factory.Source(uuid="123")
    mv = MainView(None)
    mv.source_list = mocker.MagicMock()
    mv.source_list.get_selected_source = mocker.MagicMock(return_value=source)
    mv.controller = mocker.MagicMock(is_authenticated=True)
    mv.show()
    scw = SourceConversationWrapper(source, mv.controller, None)
    mocker.patch("securedrop_client.gui.widgets.SourceConversationWrapper", return_value=scw)
    mv.on_source_changed()

    scw.on_conversation_deleted("123")

    assert mv.isVisible()
    assert scw.isVisible()
    assert not scw.conversation_title_bar.isHidden()
    assert not scw.reply_box.isHidden()
    assert not scw.reply_box.text_edit.isEnabled()
    assert not scw.reply_box.text_edit.placeholder.isHidden()
    assert scw.reply_box.text_edit.document().isEmpty()
    assert scw.conversation_view.isHidden()
    assert not scw.conversation_deletion_indicator.isHidden()
    assert scw.deletion_indicator.isHidden()


def test_SourceConversationWrapper_on_conversation_deleted_wrong_uuid(mocker):
    scw = SourceConversationWrapper(factory.Source(uuid="123"), mocker.MagicMock())
    scw.on_conversation_deleted("321")
    assert not scw.conversation_title_bar.isHidden()
    assert not scw.conversation_view.isHidden()
    assert not scw.reply_box.isHidden()
    assert scw.conversation_deletion_indicator.isHidden()
    assert scw.deletion_indicator.isHidden()


def test_SourceConversationWrapper__on_conversation_deletion_successful(mocker):
    scw = SourceConversationWrapper(factory.Source(uuid="123"), mocker.MagicMock())
    scw.on_conversation_deleted("123")

    scw._on_conversation_deletion_successful("123", datetime.now())

    assert not scw.conversation_title_bar.isHidden()
    assert not scw.conversation_view.isHidden()
    assert not scw.reply_box.isHidden()
    assert scw.conversation_deletion_indicator.isHidden()
    assert scw.deletion_indicator.isHidden()


def test_SourceConversationWrapper_on_conversation_deletion_failed(mocker):
    scw = SourceConversationWrapper(factory.Source(uuid="123"), mocker.MagicMock())
    scw.on_conversation_deleted("123")

    scw.on_conversation_deletion_failed("123")

    assert not scw.conversation_title_bar.isHidden()
    assert not scw.conversation_view.isHidden()
    assert not scw.reply_box.isHidden()
    assert scw.conversation_deletion_indicator.isHidden()
    assert scw.deletion_indicator.isHidden()


def test_SourceConversationWrapper_on_conversation_deletion_failed_wrong_uuid(mocker):
    scw = SourceConversationWrapper(factory.Source(uuid="123"), mocker.MagicMock())
    scw.on_conversation_deleted("123")

    scw.on_conversation_deletion_failed("321")

    assert not scw.conversation_title_bar.isHidden()
    assert scw.conversation_view.isHidden()
    assert not scw.reply_box.isHidden()
    assert not scw.conversation_deletion_indicator.isHidden()
    assert scw.deletion_indicator.isHidden()


def test_ConversationView_init(mocker, homedir):
    """
    Ensure the conversation view has a layout to add widgets to.
    """
    mocked_source = mocker.MagicMock()
    message = factory.Message(source=factory.Source(), content=">^..^<")
    mocked_source.collection = mocked_source.server_collection = [message]
    user = factory.User()
    mocked_controller = mocker.MagicMock(authenticated_user=user)
    cv = ConversationView(mocked_source, mocked_controller)
    assert isinstance(cv.scroll.conversation_layout, QVBoxLayout)


def test_ConversationView_init_with_deleted_source(mocker, homedir, session):
    """
    Ensure the conversation view has a layout to add widgets to.
    """
    mocked_controller = mocker.MagicMock()
    debug_logger = mocker.patch("securedrop_client.gui.widgets.logger.debug")

    def collection_error():
        raise sqlalchemy.exc.InvalidRequestError()

    source = factory.Source(uuid="ire-123")
    session.add(source)
    session.commit()

    mock_collection = mocker.patch(
        "securedrop_client.db.Source.collection", new_callable=PropertyMock
    )
    ire = sqlalchemy.exc.InvalidRequestError()
    mock_collection.side_effect = ire
    ConversationView(source, mocked_controller)
    debug_logger.assert_any_call("Error initializing ConversationView: %s", ire)


def test_ConversationView_ConversationScrollArea_resize(mocker):
    """
    Test that the resize event handler calls adjust_width on each conversation item, passing in the
    width of the scroll widget.
    """
    file = factory.File(source=factory.Source(), is_downloaded=True)
    user = factory.User()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file, authenticated_user=user)

    cv = ConversationView(factory.Source(), controller)
    message = factory.Message(source=factory.Source(), content=">^..^<")
    cv.add_message(message=message, index=0)
    speech_bubble_adjust_width = mocker.patch(
        "securedrop_client.gui.widgets.SpeechBubble.adjust_width"
    )
    cv.add_file(file=file, index=1)
    file_widget_adjust_width = mocker.patch("securedrop_client.gui.widgets.FileWidget.adjust_width")

    cv.setFixedWidth(800)
    event = QResizeEvent(cv.scroll.size(), QSize(123_456_789, 123_456_789))
    cv.scroll.resizeEvent(event)

    assert cv.scroll.widget().width() == cv.scroll.width()
    speech_bubble_adjust_width.assert_called_with(cv.scroll.widget().width())
    file_widget_adjust_width.assert_called_with(cv.scroll.widget().width())


def test_ConversationView__on_sync_started(mocker, session):
    cv = ConversationView(factory.Source(), mocker.MagicMock())
    timestamp = datetime.now()
    cv._on_sync_started(timestamp)
    assert cv.sync_started_timestamp == timestamp


def test_ConversationView__on_conversation_deletion_successful(mocker, session):
    source = factory.Source()
    message = factory.Message(source=source)
    session.add(message)
    session.add(source)
    session.commit()
    user = factory.User()
    cv = ConversationView(source, mocker.MagicMock(authenticated_user=user))
    timestamp = datetime.now()

    cv._on_conversation_deletion_successful(cv.source.uuid, timestamp)

    assert cv.deletion_scheduled_timestamp == timestamp
    assert cv.scroll.isHidden()
    assert cv.deleted_conversation_items_marker.isHidden()
    assert not cv.deleted_conversation_marker.isHidden()
    assert cv.current_messages[message.uuid].isHidden()


def test_ConversationView__on_conversation_deletion_successful_with_mismatched_source_uuid(mocker):
    """
    If the success signal was emitted for a different source, ensure the deletion markers are not
    altered.
    """
    source = factory.Source(uuid="abc123")
    cv = ConversationView(source, mocker.MagicMock())

    assert not cv.scroll.isHidden()
    assert cv.deleted_conversation_items_marker.isHidden()
    assert cv.deleted_conversation_marker.isHidden()

    cv._on_conversation_deletion_successful("notabc123", datetime.now())

    assert not cv.scroll.isHidden()
    assert cv.deleted_conversation_items_marker.isHidden()
    assert cv.deleted_conversation_marker.isHidden()


def test_ConversationView__on_conversation_deletion_successful_handles_exception(mocker, session):
    cv = ConversationView(factory.Source(uuid="abc123"), mocker.MagicMock())
    cv.source = DeletedSource()
    cv._on_conversation_deletion_successful("abc123", datetime.now())  # does not raise exception


def test_ConversationView__on_conversation_deletion_successful_does_not_hide_draft(mocker, session):
    source = factory.Source()
    user = factory.User()
    message = factory.Message(source=source)
    draft_reply = factory.DraftReply(source=source, send_status=factory.ReplySendStatus())
    session.add(draft_reply)
    session.add(message)
    session.add(source)
    session.commit()
    cv = ConversationView(source, mocker.MagicMock(authenticated_user=user))

    cv._on_conversation_deletion_successful(cv.source.uuid, datetime.now())

    assert not cv.scroll.isHidden()
    assert not cv.deleted_conversation_items_marker.isHidden()
    assert cv.deleted_conversation_marker.isHidden()
    assert cv.current_messages[message.uuid].isHidden()
    assert not cv.current_messages[draft_reply.uuid].isHidden()


def test_ConversationView_update_conversation_position_follow(mocker, homedir):
    """
    Check the signal handler sets the correct value for the scrollbar to be
    the maximum possible value, when the scrollbar is near the bottom, meaning
    it is following the conversation. This should only work if the user has
    submitted a reply to a source.
    """
    mocked_source = mocker.MagicMock()
    message = factory.Message(source=factory.Source(), content=">^..^<")
    mocked_source.collection = mocked_source.server_collection = [message]

    user = factory.User()
    mocked_controller = mocker.MagicMock(authenticated_user=user)

    cv = ConversationView(mocked_source, mocked_controller)

    # Flag to denote a reply was sent by the user.
    cv.reply_flag = True

    cv.scroll.verticalScrollBar().value = mocker.MagicMock(return_value=5900)
    cv.scroll.viewport().height = mocker.MagicMock(return_value=500)
    cv.scroll.verticalScrollBar().setValue = mocker.MagicMock()

    cv.update_conversation_position(0, 6000)

    cv.scroll.verticalScrollBar().setValue.assert_called_once_with(6000)


def test_ConversationView_update_conversation_position_stay_fixed(mocker, homedir):
    """
    Check the signal handler does not change the conversation position when
    journalist is reading older messages
    """
    mocked_source = mocker.MagicMock()
    message = factory.Message(source=factory.Source(), content=">^..^<")
    mocked_source.collection = mocked_source.server_collection = [message]

    user = factory.User()
    mocked_controller = mocker.MagicMock(authenticated_user=user)

    cv = ConversationView(mocked_source, mocked_controller)

    cv.scroll.verticalScrollBar().value = mocker.MagicMock(return_value=5500)
    cv.scroll.viewport().height = mocker.MagicMock(return_value=500)
    cv.scroll.verticalScrollBar().setValue = mocker.MagicMock()

    cv.update_conversation_position(0, 6000)

    cv.scroll.verticalScrollBar().setValue.assert_not_called()


def test_ConversationView_add_message(mocker, session, session_maker, homedir):
    """
    Adding a message results in a new MessageWidget added to the layout.
    """
    controller = logic.Controller(
        "http://localhost", mocker.MagicMock(), session_maker, homedir, None
    )
    controller.authenticated_user = factory.User()
    source = factory.Source()
    message = factory.Message(source=source, content=">^..^<")
    session.add(message)
    session.commit()

    cv = ConversationView(source, controller)
    cv.add_message(message=message, index=0)

    # Check that we added the correct widget to the layout
    message_widget = cv.scroll.conversation_layout.itemAt(1).widget()
    assert isinstance(message_widget, MessageWidget)

    assert message_widget.message.text() == ">^..^<"
    assert not message_widget.failed_to_decrypt
    assert message_widget.uuid == message.uuid
    assert message_widget.index == 0


def test_ConversationView_add_message_no_content(mocker, session, session_maker, homedir):
    """
    Adding a message results in a new MessageWidget added to the layout. This case specifically
    checks that if a `Message` has `content = None` that a helpful message is displayed as would
    be the case if download/decryption never occurred or failed.
    """
    controller = logic.Controller(
        "http://localhost", mocker.MagicMock(), session_maker, homedir, None
    )
    controller.authenticated_user = factory.User()
    source = factory.Source()
    message = factory.Message(source=source, is_decrypted=False, content=None)
    session.add(message)
    session.commit()

    cv = ConversationView(source, controller)
    cv.add_message(message=message, index=0)

    # Check that we added the correct widget to the layout
    message_widget = cv.scroll.conversation_layout.itemAt(1).widget()
    assert isinstance(message_widget, MessageWidget)

    assert message_widget.message.text() == "<Message not yet available>"
    assert not message_widget.failed_to_decrypt
    assert message_widget.uuid == message.uuid
    assert message_widget.index == 0


def test_ConversationView_on_reply_sent(mocker):
    """
    The handler for new replies should call add_reply
    """
    source = factory.Source()
    controller = mocker.MagicMock()
    controller.authenticated_user = factory.User()
    cv = ConversationView(source, controller)
    cv.update_conversation = mocker.MagicMock()

    assert cv.reply_flag is False
    cv.on_reply_sent(source_uuid=source.uuid)

    cv.update_conversation.assert_called_with(source.collection)
    assert cv.reply_flag is True


def test_ConversationView_on_reply_sent_does_not_add_message_intended_for_different_source(mocker):
    """
    The handler for new replies should not call add_reply for a message that was intended for a
    different source. #sanity-check
    """
    source = factory.Source()
    controller = mocker.MagicMock()
    cv = ConversationView(source, controller)
    cv.add_reply = mocker.MagicMock()

    cv.on_reply_sent("different_source_id")

    assert not cv.add_reply.called


def test_ConversationView_on_reply_sent_with_deleted_source(mocker):
    """
    Check that replying to a deleted source handles exception.
    """
    source = factory.Source()
    controller = mocker.MagicMock()
    cv = ConversationView(source, controller)
    cv.update_conversation = mocker.MagicMock()

    def collection_error():
        raise sqlalchemy.exc.InvalidRequestError()

    mock_collection = mocker.patch(
        "securedrop_client.db.Source.collection", new_callable=PropertyMock
    )
    ire = sqlalchemy.exc.InvalidRequestError()
    mock_collection.side_effect = ire

    cv.on_reply_sent(source.uuid)


def test_ConversationView_add_reply(mocker, homedir, session, session_maker):
    """
    Adding a reply from a source results in a new ReplyWidget added to the layout.
    """
    controller = logic.Controller(
        "http://localhost", mocker.MagicMock(), session_maker, homedir, None
    )
    controller.authenticated_user = factory.User()
    source = factory.Source()
    sender = factory.User()
    reply = factory.Reply(uuid="abc123", source=source, content=">^..^<")
    reply.journalist = sender
    session.add(reply)
    session.commit()

    cv = ConversationView(source, controller)
    cv.add_reply(reply=reply, sender=sender, index=0)

    # Check that we added the correct widget to the layout
    reply_widget = cv.scroll.conversation_layout.itemAt(1).widget()
    assert isinstance(reply_widget, ReplyWidget)

    assert reply_widget.uuid == "abc123"
    assert reply_widget.message.text() == ">^..^<"
    assert reply_widget.index == 0
    assert reply_widget.status == "SUCCEEDED"
    assert not reply_widget.failed_to_decrypt
    assert reply_widget.controller == controller
    assert not reply_widget.sender_is_current_user
    assert cv.current_messages[reply.uuid].sender == reply.journalist
    assert reply_widget.sender == sender


def test_ConversationView_add_reply_no_content(mocker, homedir, session_maker, session):
    """
    Adding a reply results in a new ReplyWidget added to the layout. This case specifically
    checks that if a `Reply` has `content = None` that a helpful message is displayed as would
    be the case if download/decryption never occurred or failed.
    """
    controller = logic.Controller(
        "http://localhost", mocker.MagicMock(), session_maker, homedir, None
    )
    controller.authenticated_user = factory.User()
    source = factory.Source()
    sender = factory.User()
    reply = factory.Reply(uuid="abc123", source=source, is_decrypted=False, content=None)
    reply.journalist = sender
    session.add(reply)
    session.commit()

    cv = ConversationView(source, controller)
    cv.add_reply(reply=reply, sender=sender, index=0)

    # Check that we added the correct widget to the layout
    reply_widget = cv.scroll.conversation_layout.itemAt(1).widget()
    assert isinstance(reply_widget, ReplyWidget)

    assert reply_widget.uuid == "abc123"
    assert reply_widget.message.text() == "<Reply not yet available>"
    assert reply_widget.index == 0
    assert reply_widget.status == "SUCCEEDED"
    assert not reply_widget.failed_to_decrypt
    assert reply_widget.controller == controller
    assert not reply_widget.sender_is_current_user
    assert cv.current_messages[reply.uuid].sender == reply.journalist
    assert reply_widget.sender == sender


def test_ConversationView_add_reply_that_has_current_user_as_sender(
    mocker, session, session_maker, homedir
):
    """
    Adding a reply from a source results in a new ReplyWidget added to the layout.
    """
    authenticated_user = factory.User()
    controller = logic.Controller(
        "http://localhost", mocker.MagicMock(), session_maker, homedir, None
    )
    controller.authenticated_user = authenticated_user
    source = factory.Source()
    reply = factory.Reply(uuid="abc123", source=source, content=">^..^<")
    reply.journalist = authenticated_user
    session.add(reply)
    session.commit()

    cv = ConversationView(source, controller)
    cv.add_reply(reply=reply, sender=authenticated_user, index=0)

    # Check that we added the correct widget to the layout
    reply_widget = cv.scroll.conversation_layout.itemAt(1).widget()
    assert isinstance(reply_widget, ReplyWidget)

    assert reply_widget.uuid == "abc123"
    assert reply_widget.message.text() == ">^..^<"
    assert reply_widget.index == 0
    assert reply_widget.status == "SUCCEEDED"
    assert not reply_widget.failed_to_decrypt
    assert reply_widget.controller == controller
    assert reply_widget.sender_is_current_user
    assert cv.current_messages[reply.uuid].sender == reply.journalist
    assert reply_widget.sender == controller.authenticated_user


def test_ConversationView_add_downloaded_file(mocker, homedir, source, session):
    """
    Adding a file results in a new FileWidget added to the layout with the
    proper QLabel.
    """

    source = source["source"]
    file = factory.File(source=source, is_downloaded=True)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    cv = ConversationView(source, controller)
    cv.conversation_updated = mocker.MagicMock()

    mock_label = mocker.patch("securedrop_client.gui.widgets.SecureQLabel")
    mocker.patch("securedrop_client.gui.widgets.QHBoxLayout.addWidget")

    cv.add_file(file, 0)

    mock_label.assert_called_with("123B")  # default factory filesize
    assert cv.conversation_updated.emit.call_count == 1

    file_widget = cv.scroll.conversation_layout.itemAt(1).widget()
    assert isinstance(file_widget, FileWidget)


def test_ConversationView_add_not_downloaded_file(mocker, homedir, source, session):
    """
    Adding a file results in a new FileWidget added to the layout with the
    proper QLabel.
    """
    source = source["source"]
    file = factory.File(source=source, is_downloaded=False, is_decrypted=None)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    cv = ConversationView(source, controller)
    cv.conversation_updated = mocker.MagicMock()

    mock_label = mocker.patch("securedrop_client.gui.widgets.SecureQLabel")
    mocker.patch("securedrop_client.gui.widgets.QHBoxLayout.addWidget")

    cv.add_file(file, 0)

    mock_label.assert_called_with("123B")  # default factory filesize
    assert cv.conversation_updated.emit.call_count == 1

    file_widget = cv.scroll.conversation_layout.itemAt(1).widget()
    assert isinstance(file_widget, FileWidget)


def test_DeleteSource_from_source_menu_when_user_is_loggedout(mocker):
    mock_controller = mocker.MagicMock()
    mock_controller.api = None
    mock_source = mocker.MagicMock()
    mock_delete_source_dialog_instance = mocker.MagicMock(DeleteSourceDialog)
    mock_delete_source_dialog = mocker.MagicMock()
    mock_delete_source_dialog.return_value = mock_delete_source_dialog_instance

    mocker.patch("securedrop_client.gui.source.DeleteSourceDialog", mock_delete_source_dialog)
    source_menu = SourceMenu(mock_source, mock_controller, None)
    source_menu.actions()[2].trigger()
    mock_delete_source_dialog_instance.exec.assert_not_called()


def test_ReplyBoxWidget_init(mocker):
    """
    Ensure reply box set up properly.
    """
    rb = ReplyBoxWidget(factory.Source(), mocker.MagicMock())
    assert rb.text_edit.isEnabled()
    assert not rb.send_button.isHidden()
    assert rb.send_button.isDefault() is True  # Needed for "Enter" to work.
    assert rb.send_button.shortcut().toString() == "Ctrl+Return"


def test_ReplyBoxWidget_init_no_auth(mocker):
    """
    Ensure reply box set up properly.
    """
    controller = mocker.MagicMock()
    controller.is_authenticated = False
    rb = ReplyBoxWidget(factory.Source(), controller)
    assert not rb.text_edit.isEnabled()
    assert rb.send_button.isHidden()


def test_ReplyBoxWidget_placeholder_show_currently_selected_source(mocker):
    """
    Ensure placeholder of replybox "Compose a reply to [source designation]" displays the
    designation for the correct source. #sanity-check
    """
    controller = mocker.MagicMock()
    source = factory.Source()
    source.journalist_designation = "source name"

    rb = ReplyBoxWidget(source, controller)

    source_name = rb.text_edit.placeholder.signed_in.layout().itemAt(1).widget()
    assert -1 != source_name.text()


def test_ReplyBoxWidget_send_reply(mocker):
    """
    Ensure sending a reply from the reply box emits signal, clears text box, and sends the reply
    details to the controller.
    """
    source = factory.Source(uuid="abc123")
    reply_uuid = "456xyz"
    mocker.patch("securedrop_client.gui.widgets.uuid4", return_value=reply_uuid)
    controller = mocker.MagicMock()
    mocker.patch("securedrop_client.gui.widgets.SourceProfileShortWidget")
    mocker.patch("securedrop_client.gui.widgets.QVBoxLayout.addWidget")
    scw = SourceConversationWrapper(source, controller, None)
    on_reply_sent_fn = mocker.MagicMock()
    scw.conversation_view.on_reply_sent = on_reply_sent_fn
    scw.reply_box.reply_sent = mocker.MagicMock()
    scw.reply_box.text_edit = ReplyTextEdit(source, controller)
    scw.reply_box.text_edit.setText = mocker.MagicMock()
    scw.reply_box.text_edit.setPlainText("Alles für Alle")

    scw.reply_box.send_reply()

    scw.reply_box.reply_sent.emit.assert_called_once_with("abc123")
    scw.reply_box.text_edit.setText.assert_called_once_with("")
    controller.send_reply.assert_called_once_with("abc123", "456xyz", "Alles für Alle")


def test_ReplyBoxWidget_send_reply_calls_setText_after_send(mocker):
    """
    Ensure sending a reply from the reply box emits signal, clears text box, and sends the reply
    details to the controller.
    """
    source = factory.Source()
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.text_edit = ReplyTextEdit(source, controller)
    setText = mocker.patch.object(rb.text_edit, "setText")
    rb.text_edit.setPlainText("Alles für Alle")

    rb.send_reply()

    setText.assert_called_once_with("")


def test_ReplyBoxWidget_send_reply_does_not_send_empty_string(mocker):
    """
    Ensure sending a reply from the reply box does not send empty string.
    """
    source = factory.Source()
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.text_edit = ReplyTextEdit(source, controller)
    assert not rb.text_edit.toPlainText()

    rb.send_reply()

    assert not controller.send_reply.called

    # Also check that we don't send blank space
    rb.text_edit.setText("  \n\n  ")

    rb.send_reply()

    assert not controller.send_reply.called


def test_ReplyBoxWidget_test_refocus_after_sync(mocker):
    source = factory.Source()
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.text_edit.hasFocus = mocker.MagicMock(return_value=True)
    rb.text_edit.setFocus = mocker.MagicMock()

    rb._on_sync_started(mocker.MagicMock())
    assert rb.refocus_after_sync is True

    rb._on_sync_succeeded()
    rb.text_edit.setFocus.assert_called_once_with()

    rb.text_edit.hasFocus.return_value = False
    rb._on_sync_started(mocker.MagicMock())
    assert rb.refocus_after_sync is False


def test_ReplyBoxWidget_on_sync_source_deleted(mocker, source):
    s = source["source"]
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(s, controller)

    debug_logger = mocker.patch("securedrop_client.gui.widgets.logger.debug")

    def pretend_source_was_deleted(self):
        raise sqlalchemy.orm.exc.ObjectDeletedError(attributes.instance_state(s), None)

    uas = mocker.patch.object(ReplyBoxWidget, "update_authentication_state")
    uas.side_effect = pretend_source_was_deleted
    rb._on_sync_started(mocker.MagicMock())
    rb._on_sync_succeeded()

    exception_str = str(sqlalchemy.orm.exc.ObjectDeletedError(attributes.instance_state(s), None))
    debug_logger.assert_called_with(
        f"During sync, ReplyBoxWidget found its source had been deleted: {exception_str}"
    )
    assert debug_logger.call_count == 2


def test_ReplyWidget_success_failure_slots(mocker):
    mock_update_signal = mocker.Mock()
    mock_download_failure_signal = mocker.Mock()
    mock_success_signal = mocker.Mock()
    mock_failure_signal = mocker.Mock()
    controller = mocker.MagicMock(authentication_state=mocker.MagicMock())
    sender = factory.User()
    widget = ReplyWidget(
        controller=controller,
        message_uuid="dummy_uuid",
        message="dummy_message",
        reply_status="PENDING",
        update_signal=mock_update_signal,
        download_error_signal=mock_download_failure_signal,
        message_succeeded_signal=mock_success_signal,
        message_failed_signal=mock_failure_signal,
        index=0,
        container_width=123,
        sender=sender,
        sender_is_current_user=False,
        failed_to_decrypt=False,
    )

    # ensure we have connected the slots
    mock_success_signal.connect.assert_called_once_with(widget._on_reply_success)
    mock_failure_signal.connect.assert_called_once_with(widget._on_reply_failure)
    assert mock_update_signal.connect.called  # to ensure no stale mocks
    assert mock_download_failure_signal.connect.called

    # check the success slog
    widget._on_reply_success("mock_source_id", "dummy_uuid" + "x", "dummy_message")
    assert widget.error.isHidden()
    widget._on_reply_success("mock_source_id", "dummy_uuid", "dummy_message")
    assert widget.error.isHidden()

    # check the failure slot where message id does not match
    widget._on_reply_failure("dummy_uuid" + "x")
    assert widget.error.isHidden()
    # check the failure slot where message id matches
    widget._on_reply_failure("dummy_uuid")
    assert not widget.error.isHidden()


def test_ReplyBoxWidget__on_authentication_changed(mocker, homedir):
    """
    When the client is authenticated, enable reply box.
    """
    source = factory.Source()
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.set_logged_in = mocker.MagicMock()

    rb._on_authentication_changed(True)

    rb.set_logged_in.assert_called_once_with()


def test_ReplyBoxWidget_on_authentication_changed_source_deleted(mocker, source):
    s = source["source"]
    co = mocker.MagicMock()
    rb = ReplyBoxWidget(s, co)

    debug_logger = mocker.patch("securedrop_client.gui.widgets.logger.debug")

    mocker.patch(
        "securedrop_client.gui.widgets.ReplyBoxWidget.update_authentication_state",
        side_effect=sqlalchemy.orm.exc.ObjectDeletedError(attributes.instance_state(s), None),
    )
    rb._on_authentication_changed(True)
    debug_logger.assert_called_once_with(
        "On authentication change, ReplyBoxWidget found its source had been deleted."
    )


def test_ReplyBoxWidget__on_authentication_changed_offline(mocker, homedir):
    """
    When the client goes offline, disable reply box.
    """
    source = factory.Source()
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.set_logged_out = mocker.MagicMock()

    rb._on_authentication_changed(False)

    rb.set_logged_out.assert_called_once_with()


def test_ReplyBoxWidget_auth_signals(mocker, homedir):
    """
    Ensure we connect to the auth signal and set the initial state on update
    """
    connect = mocker.MagicMock()
    signal = mocker.MagicMock(connect=connect)
    controller = mocker.MagicMock(authentication_state=signal)
    controller.is_authenticated = False

    _on_authentication_changed_fn = mocker.patch.object(
        ReplyBoxWidget, "_on_authentication_changed"
    )

    ReplyBoxWidget(factory.Source(), controller)

    connect.assert_called_once_with(_on_authentication_changed_fn)


def test_ReplyBoxWidget_enable(mocker):
    source = factory.Source()
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.text_edit = ReplyTextEdit(source, controller)
    rb.text_edit.set_logged_in = mocker.MagicMock()
    rb.send_button = mocker.MagicMock()

    rb.set_logged_in()

    assert rb.text_edit.toPlainText() == ""
    rb.text_edit.set_logged_in.assert_called_once_with()
    rb.send_button.show.assert_called_once_with()


def test_ReplyBoxWidget_disable(mocker):
    source = factory.Source()
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.text_edit = ReplyTextEdit(source, controller)
    rb.text_edit.set_logged_out = mocker.MagicMock()
    rb.send_button = mocker.MagicMock()

    rb.set_logged_out()

    assert rb.text_edit.toPlainText() == ""
    rb.text_edit.set_logged_out.assert_called_once_with()
    rb.send_button.hide.assert_called_once_with()


def test_ReplyBoxWidget_enable_after_source_gets_key(mocker, session, session_maker, homedir):
    """
    Test that it's enabled when a source that lacked a key now has one.
    """

    mocker.patch("sdclientapi.API")
    mock_gui = mocker.MagicMock()
    controller = logic.Controller("http://localhost", mock_gui, session_maker, homedir, None)
    controller.is_authenticated = True

    # create source without key or fingerprint
    source = factory.Source(public_key=None, fingerprint=None)
    session.add(source)
    session.commit()

    # when the ReplyBoxWidget is constructed, the source has no key,
    # so the widget should be disabled
    rbw = ReplyBoxWidget(source, controller)
    assert rbw.source.fingerprint is None
    assert rbw.source.public_key is None
    assert rbw.replybox.isEnabled() is False
    assert rbw.text_edit.isEnabled() is False

    # now simulate a sync...
    source_with_key = factory.RemoteSource(uuid=source.uuid)

    # passing 'None' for skip_uuid, test that separately
    storage.update_sources([source_with_key], [source], [], [], session, homedir)

    # ... simulate the ReplyBoxWidget receiving the sync success signal
    rbw._on_sync_succeeded()

    # ... and the widget should be enabled
    assert rbw.source.fingerprint
    assert rbw.source.public_key
    assert rbw.replybox.isEnabled()
    assert rbw.text_edit.isEnabled()


def test_ReplyTextEdit_focus_change_no_text(mocker):
    """
    Tests if placeholder text in reply box disappears when it's focused (clicked)
    and reappears when it's no longer on focus
    """
    source = factory.Source()
    controller = mocker.MagicMock()
    rt = ReplyTextEdit(source, controller)

    focus_in_event = QFocusEvent(QEvent.FocusIn)
    focus_out_event = QFocusEvent(QEvent.FocusOut)

    rt.focusInEvent(focus_in_event)
    assert rt.placeholder.isHidden()
    assert rt.toPlainText() == ""

    rt.focusOutEvent(focus_out_event)
    assert not rt.placeholder.isHidden()
    assert rt.toPlainText() == ""


def test_ReplyTextEdit_focus_change_with_text_typed(mocker):
    """
    Test that the placeholder does not appear when there is text in the ReplyTextEdit widget and
    that the text remains in the ReplyTextEdit regardless of focus.
    """
    controller = mocker.MagicMock()
    rt = ReplyTextEdit(factory.Source(), controller)
    reply_text = "mocked reply text"
    rt.setText(reply_text)

    focus_in_event = QFocusEvent(QEvent.FocusIn)
    focus_out_event = QFocusEvent(QEvent.FocusOut)

    rt.focusInEvent(focus_in_event)
    assert rt.placeholder.isHidden()
    assert rt.toPlainText() == reply_text

    rt.focusOutEvent(focus_out_event)
    assert rt.placeholder.isHidden()
    assert rt.toPlainText() == reply_text


def test_ReplyTextEdit_setText(mocker):
    """
    Checks that a non-empty string parameter causes placeholder to hide and that super's
    setPlainText method is called (to ensure cursor is hidden).
    """
    rt = ReplyTextEdit(factory.Source(), mocker.MagicMock())
    mocker.patch("securedrop_client.gui.widgets.QPlainTextEdit.setPlainText")

    rt.setText("mocked reply text")

    assert rt.placeholder.isHidden()
    rt.setPlainText.assert_called_once_with("mocked reply text")


def test_ReplyTextEdit_setText_empty_string(mocker):
    """
    Checks that plain string parameter causes placeholder to show and that super's setPlainText
    method is called (to ensure cursor is hidden).
    """
    rt = ReplyTextEdit(factory.Source(), mocker.MagicMock())
    mocker.patch("securedrop_client.gui.widgets.QPlainTextEdit.setPlainText")

    rt.setText("")

    assert not rt.placeholder.isHidden()
    rt.setPlainText.assert_called_once_with("")


def test_ReplyTextEdit_set_logged_out(mocker):
    """
    Checks the placeholder text for reply box is correct for offline mode
    """
    source = factory.Source()
    controller = mocker.MagicMock()
    rt = ReplyTextEdit(source, controller)

    rt.set_logged_out()

    sign_in = rt.placeholder.signed_out.layout().itemAt(0).widget()
    to_compose_reply = rt.placeholder.signed_out.layout().itemAt(1).widget()

    assert "Sign in" == sign_in.text()
    assert " to compose or send a reply" in to_compose_reply.text()


def test_ReplyTextEdit_set_logged_in(mocker):
    """
    Checks the placeholder text for reply box is correct for online mode
    """
    source = factory.Source()
    controller = mocker.MagicMock()
    rt = ReplyTextEdit(source, controller)

    rt.set_logged_in()

    compose_a_reply_to = rt.placeholder.signed_in.layout().itemAt(0).widget()
    source_name = rt.placeholder.signed_in.layout().itemAt(1).widget()
    assert "Compose a reply to " == compose_a_reply_to.text()
    assert source.journalist_designation == source_name.text()


def test_ReplyBox_set_logged_in_no_public_key(mocker):
    """
    If the selected source has no public key, ensure a warning message is
    shown and the user is unable to send a reply.
    """
    source = factory.Source()
    source.public_key = None
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)

    rb.set_logged_in()

    awaiting_key = rb.text_edit.placeholder.signed_in_no_key.layout().itemAt(0).widget()
    from_server = rb.text_edit.placeholder.signed_in_no_key.layout().itemAt(1).widget()

    assert "Awaiting encryption key" == awaiting_key.text()
    assert " from server to enable replies" == from_server.text()

    # Both the reply box and the text editor must be disabled for the widget
    # to be rendered correctly.
    assert rb.replybox.isEnabled() is False
    assert rb.text_edit.isEnabled() is False


def test_ReplyBox_resize_adjusts_label_width(mocker):
    """
    If the reply widget is resized, the source designation's maximum width is
    updated, and text is elided if necessary.
    """
    source = factory.Source()
    source.journalist_designation = "omniscient hippopotamus"
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.set_logged_in()

    # The widget must be displayed for the resize event to be triggered.
    rb.show()

    # We wrap the update_label_width method so we can verify that it has been
    # called while preserving its behavior.
    wrapped_update = mocker.patch.object(
        ReplyTextEditPlaceholder,
        "update_label_width",
        wraps=rb.text_edit.placeholder.update_label_width,
    )
    rb.resize(1000, rb.height())
    wrapped_update.assert_called_with(rb.text_edit.width() - 2)
    assert rb.text_edit.placeholder.source_name_label.elided is False
    rb.resize(500, rb.height())
    wrapped_update.assert_called_with(rb.text_edit.width() - 2)
    assert rb.text_edit.placeholder.source_name_label.elided is True

    rb.hide()


def test_update_conversation_maintains_old_items(mocker, session):
    """
    Calling update_conversation maintains old item state / position if there's
    no change to the conversation collection.
    """
    source = factory.Source()
    session.add(source)
    session.commit()

    file = factory.File(filename="1-source-doc.gpg", source=source)
    session.add(file)
    message = factory.Message(filename="2-source-msg.gpg", source=source)
    session.add(message)
    reply = factory.Reply(filename="3-source-reply.gpg", source=source)
    session.add(reply)
    session.commit()

    user = factory.User()
    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file, authenticated_user=user)

    cv = ConversationView(source, controller)
    assert cv.scroll.conversation_layout.count() == 3

    cv.update_conversation(cv.source.collection)

    assert cv.scroll.conversation_layout.count() == 3


def test_update_conversation_does_not_remove_pending_draft_items(mocker, session):
    """
    Calling update_conversation should not remove items that were added as drafts that were
    not converted to successful replies.
    """
    source = factory.Source()
    session.add(source)
    send_status = factory.ReplySendStatus()
    session.add(send_status)
    session.commit()

    file = factory.File(filename="1-source-doc.gpg", source=source)
    session.add(file)
    message = factory.Message(filename="2-source-msg.gpg", source=source)
    session.add(message)
    draft_reply = factory.DraftReply(source=source, send_status=send_status)
    session.add(draft_reply)
    session.commit()

    user = factory.User()
    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file, authenticated_user=user)

    cv = ConversationView(source, controller)
    assert cv.scroll.conversation_layout.count() == 3  # precondition with draft

    # add the new message and persist
    new_message = factory.Message(filename="4-source-msg.gpg", source=source)
    session.add(new_message)
    session.commit()

    # New message added, draft message persists.
    cv.update_conversation(cv.source.collection)
    assert cv.scroll.conversation_layout.count() == 4


def test_update_conversation_does_remove_successful_draft_items(mocker, session):
    """
    Calling update_conversation should remove items that were added as drafts that were
    converted to successful replies.
    """
    source = factory.Source()
    session.add(source)
    send_status = factory.ReplySendStatus()
    session.add(send_status)
    session.commit()

    file = factory.File(filename="1-source-doc.gpg", source=source)
    session.add(file)
    message = factory.Message(filename="2-source-msg.gpg", source=source)
    session.add(message)
    draft_reply = factory.DraftReply(source=source, send_status=send_status)
    session.add(draft_reply)
    session.commit()

    user = factory.User()
    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file, authenticated_user=user)

    cv = ConversationView(source, controller)
    assert cv.scroll.conversation_layout.count() == 3  # precondition with draft

    # add the new message and persist
    new_message = factory.Message(filename="4-source-msg.gpg", source=source)
    session.add(new_message)
    session.commit()

    # remove draft
    session.delete(draft_reply)
    session.commit()

    # New message added, draft message is gone.
    cv.update_conversation(cv.source.collection)
    assert cv.scroll.conversation_layout.count() == 3


def test_update_conversation_keeps_failed_draft_items(mocker, session):
    """
    Calling update_conversation keeps items that were added as drafts but which
    have failed.
    """
    user = factory.User()
    source = factory.Source()
    session.add(source)
    send_status = factory.ReplySendStatus(name="FAILED")
    session.add(send_status)
    session.commit()

    file = factory.File(filename="1-source-doc.gpg", source=source)
    session.add(file)
    message = factory.Message(filename="2-source-msg.gpg", source=source)
    session.add(message)
    draft_reply = factory.DraftReply(source=source, send_status=send_status)
    session.add(draft_reply)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file, authenticated_user=user)

    cv = ConversationView(source, controller)
    assert cv.scroll.conversation_layout.count() == 3  # precondition with draft

    # add the new message and persist
    new_message = factory.Message(filename="4-source-msg.gpg", source=source)
    session.add(new_message)
    session.commit()

    # New message added, draft message retained.
    cv.update_conversation(cv.source.collection)
    assert cv.scroll.conversation_layout.count() == 4


def test_update_conversation_adds_new_items(mocker, session):
    """
    Calling update_conversation adds new items to layout
    """
    source = factory.Source()
    session.add(source)
    session.commit()

    file = factory.File(filename="1-source-doc.gpg", source=source)
    session.add(file)
    message = factory.Message(filename="2-source-msg.gpg", source=source)
    session.add(message)
    reply = factory.Reply(filename="3-source-reply.gpg", source=source)
    session.add(reply)
    session.commit()

    user = factory.User()
    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file, authenticated_user=user)

    cv = ConversationView(source, controller)
    assert cv.scroll.conversation_layout.count() == 3  # precondition

    # add the new message and persist
    new_message = factory.Message(filename="4-source-msg.gpg", source=source)
    session.add(new_message)
    session.commit()

    cv.update_conversation(cv.source.collection)
    assert cv.scroll.conversation_layout.count() == 4


def test_update_conversation_position_updates(mocker, session):
    """
    Calling update_conversation adds new items to layout
    """
    source = factory.Source()
    session.add(source)
    session.commit()

    file = factory.File(filename="1-source-doc.gpg", source=source)
    session.add(file)
    message = factory.Message(filename="2-source-msg.gpg", source=source)
    session.add(message)
    reply = factory.Reply(filename="3-source-reply.gpg", source=source)
    session.add(reply)
    session.commit()

    user = factory.User()
    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file, authenticated_user=user)

    cv = ConversationView(source, controller)
    assert cv.scroll.conversation_layout.count() == 3  # precondition

    # Change the position of the Reply.
    reply_widget = cv.current_messages[reply.uuid]
    reply_widget.index = 1

    # add the new message and persist
    new_message = factory.Message(filename="4-source-msg.gpg", source=source)
    session.add(new_message)
    session.commit()

    cv.update_conversation(cv.source.collection)
    assert cv.scroll.conversation_layout.count() == 4
    assert reply_widget.index == 2  # re-ordered.


def test_update_conversation_content_updates(mocker, session):
    """
    Subsequent calls to update_conversation update the content of the conversation_item
    if it has changed.
    """
    user = factory.User()
    mock_controller = mocker.MagicMock(authenticated_user=user)
    # The controller's session must be a legitimate sqlalchemy session for this test
    mock_controller.session = session
    source = factory.Source()
    session.add(source)
    session.commit()

    message = factory.Message(filename="2-source-msg.gpg", source=source, content=None)
    session.add(message)
    session.commit()

    cv = ConversationView(source, mock_controller)
    cv.update_deletion_markers = mocker.MagicMock()
    cv.current_messages = {}

    cv.scroll.conversation_layout.removeWidget = mocker.MagicMock()
    mocker.patch.object(cv.scroll, "add_widget_to_conversation")

    # this is the MessageWidget that __init__() would return
    mock_msg_widget_res = mocker.MagicMock()
    # mock MessageWidget so we can inspect the __init__ call to see what content
    # is in the widget.
    mock_msg_widget = mocker.patch(
        "securedrop_client.gui.widgets.MessageWidget", return_value=mock_msg_widget_res
    )

    # First call of update_conversation: with null content
    cv.update_conversation(cv.source.collection)

    # Since the content was None, we should have created the widget
    # with the default message (which is the third call_arg).
    assert mock_msg_widget.call_args[0][1] == "<Message not yet available>"

    # Meanwhile, in another session, we add content to the database for that same message.
    engine = session.get_bind()
    second_session = scoped_session(sessionmaker(bind=engine))
    message = second_session.query(db.Message).one()
    expected_content = "now there is content here!"
    message.content = expected_content
    second_session.add(message)
    second_session.commit()

    # Second call of update_conversation
    cv.update_conversation(cv.source.collection)

    # Check that the widget was updated with the expected content.
    assert mock_msg_widget_res.message.setText.call_args[0][0] == expected_content


def test_update_conversation_updates_sender(mocker, homedir, session_maker, session):
    """
    Ensure reply sender badge is updated when the sender is not the authenticated user.
    """
    source = factory.Source()
    session.add(source)
    reply = factory.Reply(filename="3-source-reply.gpg", source=source)
    reply.journalist = factory.User()
    session.add(reply.journalist)
    session.add(reply)
    session.commit()
    controller = logic.Controller(
        "http://localhost", mocker.MagicMock(), session_maker, homedir, None
    )
    controller.authenticated_user = factory.User()
    controller.update_authenticated_user = mocker.MagicMock()
    cv = ConversationView(source, controller)

    cv.update_conversation(cv.source.collection)

    assert cv.current_messages[reply.uuid].sender == reply.journalist
    assert cv.current_messages[reply.uuid].sender_icon.initials == reply.journalist.initials


def test_update_conversation_calls_updates_sender_for_authenticated_user(
    mocker, homedir, session_maker, session
):
    """
    Ensure reply sender badge is updated when the sender is the authenticated user.
    """
    source = factory.Source()
    session.add(source)
    reply = factory.Reply(filename="3-source-reply.gpg", source=source)
    reply.journalist = factory.User()
    session.add(reply.journalist)
    session.add(reply)
    session.commit()
    controller = logic.Controller(
        "http://localhost", mocker.MagicMock(), session_maker, homedir, None
    )
    controller.authenticated_user = reply.journalist
    controller.update_authenticated_user = mocker.MagicMock()
    cv = ConversationView(source, controller)

    cv.update_conversation(cv.source.collection)

    assert cv.current_messages[reply.uuid].sender == reply.journalist
    assert cv.current_messages[reply.uuid].sender_icon.initials == reply.journalist.initials


def test_update_conversation_updates_sender_when_sender_changes(
    mocker, homedir, session_maker, session
):
    """
    Ensure reply sender badge is updated when the sender changes due to deletion or is updated.
    """
    source = factory.Source()
    session.add(source)
    reply = factory.Reply(filename="3-source-reply.gpg", source=source)
    reply.journalist = factory.User()
    session.add(reply.journalist)
    session.add(reply)
    session.commit()
    controller = logic.Controller(
        "http://localhost", mocker.MagicMock(), session_maker, homedir, None
    )
    controller.update_authenticated_user = mocker.MagicMock()
    cv = ConversationView(source, controller)
    cv.update_deletion_markers = mocker.MagicMock()

    cv.update_conversation(cv.source.collection)

    reply.journalist.firstname = "abc"
    reply.journalist.lastname = "123"
    cv.update_conversation(cv.source.collection)

    assert cv.current_messages[reply.uuid].sender == reply.journalist
    assert cv.current_messages[reply.uuid].sender_icon.initials == "a1"

    deleted_user_account = factory.User(username="xyz", firstname=None, lastname=None)
    reply.journalist = deleted_user_account
    session.add(reply)
    session.commit()

    cv.update_conversation(cv.source.collection)

    assert cv.current_messages[reply.uuid].sender == deleted_user_account
    assert cv.current_messages[reply.uuid].sender_icon.initials == deleted_user_account.initials


def test_update_conversation_shows_marker_when_all_items_deleted(
    mocker, homedir, session_maker, session
):
    """
    When an entire conversation is deleted, update_conversation should indicate that.
    """
    source = factory.Source()
    source.interaction_count = 5
    session.add(source)
    session.commit()
    controller = logic.Controller(
        "http://localhost", mocker.MagicMock(), session_maker, homedir, None
    )
    controller.update_authenticated_user = mocker.MagicMock()
    cv = ConversationView(source, controller)
    cv.update_conversation(cv.source.collection)
    assert cv.deleted_conversation_items_marker.isHidden()
    assert not cv.deleted_conversation_marker.isHidden()


def test_SourceProfileShortWidget_update_timestamp(mocker):
    """
    Ensure the update_timestamp slot actually updates the LastUpdatedLabel
    instance with the last_updated value from the source..
    """
    mock_controller = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    mock_source.last_updated = datetime.now()
    mock_source.journalist_designation = "wimple horse knackered unittest"
    spsw = SourceProfileShortWidget(mock_source, mock_controller, None)
    spsw.updated = mocker.MagicMock()
    spsw.update_timestamp()
    spsw.updated.setText.assert_called_once_with(
        arrow.get(mock_source.last_updated).format("MMM D")
    )


def test_SenderIcon_for_deleted_user(mocker):
    """
    Ensure reply sender badge shows image instead of initials for deleted user.
    """
    sender = factory.User(username="deleted")
    si = SenderIcon()
    si.label.setPixmap = mocker.MagicMock()

    si.initials = sender.initials

    assert si.label.setPixmap.call_count == 1


def test_SenderIcon_sets_text_to_initials(mocker):
    """
    Ensure reply sender badge sets label to initials of the sender.
    """
    sender = factory.User()
    si = SenderIcon()
    si.label.setText = mocker.MagicMock()

    si.initials = sender.initials

    si.label.setText.assert_called_once_with(sender.initials)


def test_SenderIcon_sets_text_to_initials_for_authenticated_user(mocker):
    """
    Ensure reply sender badge sets label to initials of the sender for authenticated user.
    """
    sender = factory.User()
    si = SenderIcon()
    si.label.setText = mocker.MagicMock()
    si.is_current_user = True

    si.initials = sender.initials

    si.label.setText.assert_called_once_with(sender.initials)


def test_SenderIcon_set_pending_styles_purple_for_authenticated_user(mocker):
    """
    Ensure reply sender badge is blue when the sender is not the authenticated user.
    """
    sender = factory.User()
    si = SenderIcon()
    si.setObjectName = mocker.MagicMock()
    si.is_current_user = True
    si.initials = sender.initials

    si.set_pending_styles()

    si.setObjectName.assert_called_once_with("SenderIcon_current_user_pending")


def test_SenderIcon_set_normal_styles_purple_for_authenticated_user(mocker):
    """
    Ensure reply sender badge is purple when the sender is the authenticated user.
    """
    sender = factory.User()
    si = SenderIcon()
    si.setObjectName = mocker.MagicMock()
    si.is_current_user = True
    si.initials = sender.initials

    si.set_normal_styles()

    si.setObjectName.assert_called_once_with("SenderIcon_current_user")


def test_ConversationView_updates_message_seenby_tooltip(mocker, session):
    """
    Ensure the tooltip displays the usernames of the users who have seen the messages
    in the correct order.
    """
    # Create a source, message, and a journalist that will see that message
    source = factory.Source()
    session.add(source)
    message = factory.Message(source=source)
    session.add(message)
    journalist = factory.User(username="dellsberg")
    session.add(journalist)
    session.commit()

    # Add the record that says the journalist saw the message
    session.add(db.SeenMessage(message_id=message.id, journalist_id=journalist.id))
    session.commit()

    # Create the MessageWidget for the message above
    controller = mocker.MagicMock(authenticated_user=journalist)
    cv = ConversationView(source, controller)
    cv.update_conversation(source.collection)
    message_widget = cv.current_messages[message.uuid]

    # Get the tool tip text and compare it to the expected result
    assert message_widget.check_mark.toolTip() == "dellsberg"

    # Update the conversation again after another journalist has seen the same message
    second_journalist = factory.User(username="journalist")
    session.add(second_journalist)
    session.commit()

    # Add the record that says the second journalist saw the message
    session.add(db.SeenMessage(message_id=message.id, journalist_id=second_journalist.id))
    session.commit()

    # Update the source collection
    cv.update_conversation(source.collection)

    m = mocker.MagicMock()
    dict = {journalist.username: journalist, second_journalist.username: second_journalist}
    m.__getitem__.side_effect = dict.__getitem__
    assert message_widget.check_mark.toolTip() == "journalist,\ndellsberg"


def test_ConversationView_updates_reply_seenby_tooltip(mocker, session):
    """
    Ensure the tooltip displays the usernames of the users who have seen the replies
    in the correct order.
    """
    # Create a source, message, and a journalist that will see that message
    source = factory.Source()
    session.add(source)
    reply = factory.Reply(source=source)
    session.add(reply)
    journalist = factory.User(username="dellsberg")
    session.add(journalist)
    session.commit()

    # Add the record that says the journalist saw the message
    session.add(db.SeenReply(reply_id=reply.id, journalist_id=journalist.id))
    session.commit()

    # Create the MessageWidget for the message above
    controller = mocker.MagicMock(authenticated_user=journalist)
    cv = ConversationView(source, controller)
    cv.update_conversation(source.collection)
    reply_widget = cv.current_messages[reply.uuid]

    # Get the tool tip text and compare it to the expected result
    assert reply_widget.check_mark.toolTip() == "dellsberg"

    # Update the conversation again after another journalist has seen the same message
    second_journalist = factory.User(username="journalist")
    session.add(second_journalist)
    session.commit()

    # Add the record that says the second journalist saw the message
    session.add(db.SeenReply(reply_id=reply.id, journalist_id=second_journalist.id))
    session.commit()

    # Update the source collection
    cv.update_conversation(source.collection)

    assert reply_widget.check_mark.toolTip() == "journalist,\ndellsberg"
