"""
Make sure the UI widgets are configured correctly and work as expected.
"""
import pytest
import arrow
from datetime import datetime
from unittest.mock import patch

from PyQt5.QtCore import Qt, QEvent
from PyQt5.QtGui import QFocusEvent, QKeyEvent, QMovie
from PyQt5.QtTest import QTest
from PyQt5.QtWidgets import QWidget, QApplication, QVBoxLayout, QMessageBox, QMainWindow, \
    QLineEdit
import sqlalchemy
import sqlalchemy.orm.exc
from sqlalchemy.orm import attributes, scoped_session, sessionmaker

from securedrop_client import db, logic, storage
from securedrop_client.export import ExportError, ExportStatus
from securedrop_client.gui.widgets import MainView, SourceList, SourceWidget, SecureQLabel, \
    LoginDialog, SpeechBubble, MessageWidget, ReplyWidget, FileWidget, ConversationView, \
    DeleteSourceMessageBox, DeleteSourceAction, SourceMenu, TopPane, LeftPane, SyncIcon, \
    ErrorStatusBar, ActivityStatusBar, UserProfile, UserButton, UserMenu, LoginButton, \
    ReplyBoxWidget, ReplyTextEdit, SourceConversationWrapper, StarToggleButton, LoginOfflineLink, \
    LoginErrorBar, EmptyConversationView, ModalDialog, ExportDialog, PrintDialog, \
    PasswordEdit, SourceProfileShortWidget, UserIconLabel
from tests import factory


app = QApplication([])


def test_TopPane_init(mocker):
    """
    Ensure the TopPane instance is correctly set up.
    """
    tp = TopPane()
    file_path = tp.sync_icon.sync_animation.fileName()
    filename = file_path[file_path.rfind('/') + 1:]
    assert filename == 'sync_disabled.gif'


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

    tp.update_activity_status(message='test message', duration=5)

    tp.activity_status_bar.update_message.assert_called_once_with('test message', 5)


def test_TopPane_update_error_status(mocker):
    """
    Calling update_error_status calls update_message on ErrorStatusBar.
    """
    tp = TopPane()
    tp.error_status_bar = mocker.MagicMock()

    tp.update_error_status(message='test message', duration=5)

    tp.error_status_bar.update_message.assert_called_once_with('test message', 5)


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
    filename = file_path[file_path.rfind('/') + 1:]
    assert filename == 'sync_disabled.gif'


def test_SyncIcon_init_starts_animiation(mocker):
    movie = QMovie()
    movie.start = mocker.MagicMock()
    mocker.patch('securedrop_client.gui.widgets.load_movie', return_value=movie)

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
    filename = file_path[file_path.rfind('/') + 1:]
    assert filename == 'sync.gif'


def test_SyncIcon_enable_starts_animiation(mocker):
    movie = QMovie()
    movie.start = mocker.MagicMock()
    mocker.patch('securedrop_client.gui.widgets.load_movie', return_value=movie)

    sync_icon = SyncIcon()
    sync_icon.enable()

    sync_icon.sync_animation.start.assert_called_with()


def test_SyncIcon_disable(mocker):
    sync_icon = SyncIcon()

    sync_icon.disable()

    file_path = sync_icon.sync_animation.fileName()
    filename = file_path[file_path.rfind('/') + 1:]
    assert filename == 'sync_disabled.gif'


def test_SyncIcon_disable_starts_animiation(mocker):
    movie = QMovie()
    movie.start = mocker.MagicMock()
    mocker.patch('securedrop_client.gui.widgets.load_movie', return_value=movie)

    sync_icon = SyncIcon()
    sync_icon.disable()

    sync_icon.sync_animation.start.assert_called_with()


def test_SyncIcon__on_sync_syncing(mocker):
    '''
    Sync icon becomes active when it receives the `syncing` signal.
    '''
    sync_icon = SyncIcon()

    sync_icon._on_sync('syncing')

    file_path = sync_icon.sync_animation.fileName()
    filename = file_path[file_path.rfind('/') + 1:]
    assert filename == 'sync_active.gif'


def test_SyncIcon__on_sync_synced(mocker):
    '''
    Sync icon becomes "inactive" when it receives the `synced` signal.
    '''
    sync_icon = SyncIcon()

    sync_icon._on_sync('synced')

    file_path = sync_icon.sync_animation.fileName()
    filename = file_path[file_path.rfind('/') + 1:]
    assert filename == 'sync.gif'


def test_SyncIcon___on_sync_with_data_not_equal_to_syncing(mocker):
    '''
    Sync does not because active when the sync signal's data is something other than 'syncing'
    '''
    movie = QMovie()
    movie.start = mocker.MagicMock()
    mocker.patch('securedrop_client.gui.widgets.load_movie', return_value=movie)
    sync_icon = SyncIcon()

    # assert that start call count has only been called once
    sync_icon.sync_animation.start.assert_called_once_with()

    sync_icon._on_sync('something other than syncing')

    # assert that _on_sync doesn't increase start call count from one
    sync_icon.sync_animation.start.assert_called_once_with()


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

    esb.update_message(message='test message', duration=123)

    esb.status_bar.showMessage.assert_called_once_with('test message', 123)
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
    asb.update_message(message='test message', duration=123)
    assert asb.currentMessage() == 'test message'


def test_UserProfile_setup(mocker):
    up = UserProfile()
    up.user_button = mocker.MagicMock()
    up.login_button = mocker.MagicMock()
    window = mocker.MagicMock()
    controller = mocker.MagicMock()

    up.setup(window, controller)

    up.user_button.setup.assert_called_once_with(controller)
    up.login_button.setup.assert_called_once_with(window)


def test_UserProfile_set_user(mocker):
    up = UserProfile()
    up.user_icon = mocker.MagicMock()
    up.user_button = mocker.MagicMock()
    user = factory.User(firstname='firstname_mock', lastname='lastname_mock')

    up.set_user(user)

    up.user_icon.setText.assert_called_with('fl')
    up.user_button.set_username.assert_called_with('firstname_mock lastname_mock')


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
    ub.set_username('test_username')
    ub.text() == 'test_username'


def test_UserButton_set_long_username(mocker):
    ub = UserButton()
    ub.setToolTip = mocker.MagicMock()
    ub.set_username('test_username_that_is_very_very_long')
    ub.setToolTip.assert_called_once_with(
        'test_username_that_is_very_very_long'
    )


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
    assert lb.text() == 'SIGN IN'


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
    mv.source_list = mocker.MagicMock()
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
    mv.source_list.source_widgets = []
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
    source = factory.Source(uuid='123')
    conversation_wrapper = SourceConversationWrapper(source, mocker.MagicMock())
    conversation_wrapper.deleteLater = mocker.MagicMock()
    mock_source_conv_wrapper_widget = mocker.MagicMock()
    mock_source_conv_wrapper_widget.deleteLater = mocker.MagicMock()
    mv = MainView(None)
    mv.source_conversations = {}
    mv.source_conversations['123'] = conversation_wrapper

    mv.delete_conversation('123')

    conversation_wrapper.deleteLater.assert_called_once_with()
    assert mv.source_conversations == {}


def test_MainView_delete_conversation_when_conv_wrapper_does_not_exist(mocker):
    """
    Ensure that delete_conversation throws no exception if the SourceConversationWrapper
    does not exist.
    """
    source_uuid = 'foo'
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
    mocker.patch('securedrop_client.gui.widgets.source_exists', return_value=True)
    scw = mocker.MagicMock()
    mocker.patch('securedrop_client.gui.widgets.SourceConversationWrapper', return_value=scw)

    mv.on_source_changed()

    mv.source_list.get_selected_source.assert_called_once_with()
    mv.set_conversation.assert_called_once_with(scw)


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
    mv.source_list = mocker.MagicMock()
    mv.controller = mocker.MagicMock(is_authenticated=True)
    s = factory.Source()
    session.add(s)
    f = factory.File(source=s, filename='0-mock-doc.gpg')
    session.add(f)
    m = factory.Message(source=s, filename='0-mock-msg.gpg')
    session.add(m)
    r = factory.Reply(source=s, filename='0-mock-reply.gpg')
    session.add(r)
    session.commit()
    mv.source_list.get_selected_source = mocker.MagicMock(return_value=s)
    add_message_fn = mocker.patch(
        'securedrop_client.gui.widgets.ConversationView.add_message', new=mocker.Mock())
    add_reply_fn = mocker.patch(
        'securedrop_client.gui.widgets.ConversationView.add_reply', new=mocker.Mock())
    add_file_fn = mocker.patch(
        'securedrop_client.gui.widgets.ConversationView.add_file', new=mocker.Mock())

    mv.on_source_changed()

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
    mv.source_list = mocker.MagicMock()
    mv.set_conversation = mocker.MagicMock()
    mv.controller = mocker.MagicMock(is_authenticated=True)
    source = factory.Source()
    source2 = factory.Source()
    session.add(source)
    session.add(source2)
    session.commit()

    source_conversation_init = mocker.patch(
        'securedrop_client.gui.widgets.SourceConversationWrapper.__init__',
        return_value=None)

    # We expect on the first call, SourceConversationWrapper.__init__ should be called.
    mv.source_list.get_selected_source = mocker.MagicMock(return_value=source)
    mv.on_source_changed()
    assert mv.set_conversation.call_count == 1
    assert source_conversation_init.call_count == 1

    # Reset mock call counts for next call of on_source_changed.
    source_conversation_init.reset_mock()
    mv.set_conversation.reset_mock()

    # Now click on another source (source2). Since this is the first time we have clicked
    # on source2, we expect on the first call, SourceConversationWrapper.__init__ should be
    # called.
    mv.source_list.get_selected_source = mocker.MagicMock(return_value=source2)
    mv.on_source_changed()
    assert mv.set_conversation.call_count == 1
    assert source_conversation_init.call_count == 1

    # Reset mock call counts for next call of on_source_changed.
    source_conversation_init.reset_mock()
    mv.set_conversation.reset_mock()

    # But if we click back (call on_source_changed again) to the source,
    # its SourceConversationWrapper should _not_ be recreated.
    mv.source_list.get_selected_source = mocker.MagicMock(return_value=source)
    conversation_wrapper = mv.source_conversations[source.uuid]
    conversation_wrapper.conversation_view = mocker.MagicMock()
    conversation_wrapper.conversation_view.update_conversation = mocker.MagicMock()

    mv.on_source_changed()

    assert mv.set_conversation.call_count == 1

    # Conversation should be redrawn even for existing source (bug #467).
    assert conversation_wrapper.conversation_view.update_conversation.call_count == 1
    assert source_conversation_init.call_count == 0


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
    mocker.patch('securedrop_client.gui.widgets.SourceWidget', mock_sw)
    mocker.patch('securedrop_client.gui.widgets.SourceListWidgetItem', mock_lwi)

    sources = [mocker.MagicMock(), mocker.MagicMock(), mocker.MagicMock(), ]
    sl.update(sources)

    assert mock_sw.call_count == len(sources)
    assert mock_lwi.call_count == len(sources)
    assert sl.insertItem.call_count == len(sources)
    assert sl.setItemWidget.call_count == len(sources)
    assert len(sl.source_widgets) == len(sources)
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
    sources = [mocker.MagicMock(), mocker.MagicMock(), mocker.MagicMock(), ]
    sl.initial_update(sources)
    sl.add_source.assert_called_once_with(sources)


def test_SourceList_update_when_source_deleted(mocker, session, session_maker, homedir):
    """
    Test that SourceWidget.update raises an exception when its source has been deleted.

    When SourceList.update calls SourceWidget.update and that
    SourceWidget's source has been deleted, SourceList.update should
    catch the resulting excpetion, delete the SourceWidget and add its
    source UUID to the list of deleted source UUIDs.
    """
    mock_gui = mocker.MagicMock()
    controller = logic.Controller('http://localhost', mock_gui, session_maker, homedir)

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
    assert len(sl.source_widgets) == 1

    # now delete it
    session.delete(source)
    session.commit()

    # and finally verify that updating raises an exception, causing
    # the SourceWidget to be deleted
    deleted_uuids = sl.update([source])
    assert len(deleted_uuids) == 1
    assert source.uuid in deleted_uuids
    assert len(sl.source_widgets) == 0


def test_SourceList_add_source_starts_timer(mocker, session_maker, homedir):
    """
    When the add_source method is called it schedules the addition of a source
    to the source list via a single-shot QTimer.
    """
    sl = SourceList()
    sources = [mocker.MagicMock(), mocker.MagicMock(), mocker.MagicMock(), ]
    mock_timer = mocker.MagicMock()
    with mocker.patch("securedrop_client.gui.widgets.QTimer", mock_timer):
        sl.add_source(sources)
    assert mock_timer.singleShot.call_count == 1


def test_SourceList_update_when_source_deleted_crash(mocker, session, session_maker, homedir):
    """
    When SourceList.update calls SourceWidget.update and that
    SourceWidget has been deleted from the dict on the SourceList,
    it should handle the exception and delete the list widget.
    """
    mock_gui = mocker.MagicMock()
    controller = logic.Controller('http://localhost', mock_gui, session_maker, homedir)

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
    assert len(sl.source_widgets) == 1
    assert sl.count() == 1

    # Remove source_widget from dict
    sl.source_widgets.pop(oss.uuid)

    # now delete it
    session.delete(source)
    session.commit()

    # and finally verify that updating does not throw an exception, and
    # all widgets are removed from the list view.
    deleted_uuids = sl.update([])
    assert sl.count() == 0


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
    mocker.patch.object(second_item, 'isSelected', return_value=True)

    sl.update([factory.Source(), factory.Source()])

    assert second_item.isSelected() is True


def test_SourceList_update_removes_selected_item_results_in_no_current_selection(mocker):
    """
    Check that no items are currently selected if the currently selected item is deleted.
    """
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    sl.update([factory.Source(uuid='new'), factory.Source(uuid='newer')])

    sl.setCurrentItem(sl.itemAt(0, 0))  # select source with uuid='newer'
    sl.update([factory.Source(uuid='new')])  # delete source with uuid='newer'

    assert not sl.currentItem()


def test_SourceList_update_removes_item_from_end_of_list(mocker):
    """
    Check that the item is removed from the source list and dict if the source no longer exists.
    """
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    sl.update([
        factory.Source(uuid='new'), factory.Source(uuid='newer'), factory.Source(uuid='newest')])
    assert sl.count() == 3
    sl.update([factory.Source(uuid='newer'), factory.Source(uuid='newest')])
    assert sl.count() == 2
    assert sl.itemWidget(sl.item(0)).source.uuid == 'newest'
    assert sl.itemWidget(sl.item(1)).source.uuid == 'newer'
    assert len(sl.source_widgets) == 2


def test_SourceList_update_removes_item_from_middle_of_list(mocker):
    """
    Check that the item is removed from the source list and dict if the source no longer exists.
    """
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    sl.update([
        factory.Source(uuid='new'), factory.Source(uuid='newer'), factory.Source(uuid='newest')])
    assert sl.count() == 3
    sl.update([factory.Source(uuid='new'), factory.Source(uuid='newest')])
    assert sl.count() == 2
    assert sl.itemWidget(sl.item(0)).source.uuid == 'newest'
    assert sl.itemWidget(sl.item(1)).source.uuid == 'new'
    assert len(sl.source_widgets) == 2


def test_SourceList_update_removes_item_from_beginning_of_list(mocker):
    """
    Check that the item is removed from the source list and dict if the source no longer exists.
    """
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    sl.update([
        factory.Source(uuid='new'), factory.Source(uuid='newer'), factory.Source(uuid='newest')])
    assert sl.count() == 3
    sl.update([factory.Source(uuid='new'), factory.Source(uuid='newer')])
    assert sl.count() == 2
    assert sl.itemWidget(sl.item(0)).source.uuid == 'newer'
    assert sl.itemWidget(sl.item(1)).source.uuid == 'new'
    assert len(sl.source_widgets) == 2


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
    mocker.patch('securedrop_client.gui.widgets.SourceWidget', mock_sw)
    mocker.patch('securedrop_client.gui.widgets.SourceListWidgetItem', mock_lwi)
    sources = [mocker.MagicMock(), mocker.MagicMock(), mocker.MagicMock(), ]
    mock_timer = mocker.MagicMock()
    with mocker.patch("securedrop_client.gui.widgets.QTimer", mock_timer):
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
        assert len(sl.source_widgets) == 1
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
    mocker.patch('securedrop_client.gui.widgets.SourceWidget', mock_sw)
    mocker.patch('securedrop_client.gui.widgets.SourceListWidgetItem', mock_lwi)
    sources = []
    mock_timer = mocker.MagicMock()
    with mocker.patch("securedrop_client.gui.widgets.QTimer", mock_timer):
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
        assert len(sl.source_widgets) == 0
        assert sl.setCurrentItem.call_count == 0
        assert sl.add_source.call_count == 0


def test_SourceList_set_snippet(mocker):
    """
    Handle the emitted event in the expected manner.
    """
    sl = SourceList()
    mock_widget = mocker.MagicMock()
    sl.source_widgets = {
        "a_uuid": mock_widget,
    }
    sl.set_snippet("a_uuid", "msg_uuid", "msg_content")
    mock_widget.set_snippet.assert_called_once_with("a_uuid", "msg_content")


def test_SourceList_get_source_widget(mocker):
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    mock_source = factory.Source(uuid='mock_uuid')
    sl.update([mock_source])
    sl.source_widgets = {}

    source_widget = sl.get_source_widget('mock_uuid')

    assert source_widget.source_uuid == 'mock_uuid'
    assert source_widget == sl.itemWidget(sl.item(0))


def test_SourceList_get_source_widget_does_not_exist(mocker):
    sl = SourceList()
    sl.controller = mocker.MagicMock()
    mock_source = factory.Source(uuid='mock_uuid')
    sl.update([mock_source])
    sl.source_widgets = {}

    source_widget = sl.get_source_widget('uuid_for_source_not_in_list')

    assert source_widget is None


def test_SourceList_get_source_widget_if_one_exists_in_cache(mocker):
    sl = SourceList()
    mock_source_widget = factory.Source(uuid='mock_uuid')
    sl.source_widgets = {'mock_uuid': mock_source_widget}
    source_widget = sl.get_source_widget('mock_uuid')
    assert source_widget == mock_source_widget


def test_SourceWidget_init(mocker):
    """
    The source widget is initialised with the passed-in source.
    """
    controller = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    mock_source.journalist_designation = 'foo bar baz'
    sw = SourceWidget(controller, mock_source)
    assert sw.source == mock_source


def test_SourceWidget_html_init(mocker):
    """
    The source widget is initialised with the given source name, with
    HTML escaped properly.
    """
    controller = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    mock_source.journalist_designation = 'foo <b>bar</b> baz'

    sw = SourceWidget(controller, mock_source)
    sw.name = mocker.MagicMock()
    sw.summary_layout = mocker.MagicMock()

    mocker.patch('securedrop_client.gui.SvgLabel')
    sw.update()

    sw.name.setText.assert_called_once_with('foo <b>bar</b> baz')


def test_SourceWidget_update_attachment_icon(mocker):
    """
    Attachment icon identicates document count
    """
    controller = mocker.MagicMock()
    source = factory.Source(document_count=1)
    sw = SourceWidget(controller, source)

    sw.update()
    assert not sw.paperclip.isHidden()

    source.document_count = 0

    sw.update()
    assert sw.paperclip.isHidden()


def test_SourceWidget_update_raises_InvalidRequestError(mocker):
    """
    If the source no longer exists in the local data store, ensure the expected
    exception is logged and re-raised.
    """
    controller = mocker.MagicMock()
    source = factory.Source(document_count=1)
    sw = SourceWidget(controller, source)
    ex = sqlalchemy.exc.InvalidRequestError()
    controller.session.refresh.side_effect = ex
    mock_logger = mocker.MagicMock()
    mocker.patch(
        "securedrop_client.gui.widgets.logger",
        mock_logger,
    )
    with pytest.raises(sqlalchemy.exc.InvalidRequestError):
        sw.update()
        assert mock_logger.error.call_count == 1


def test_SourceWidget_set_snippet_draft_only(mocker, session_maker, session, homedir):
    """
    Snippets/previews do not include draft messages.
    """
    mock_gui = mocker.MagicMock()
    controller = logic.Controller('http://localhost', mock_gui, session_maker, homedir)
    source = factory.Source(document_count=1)
    f = factory.File(source=source)
    reply = factory.DraftReply(source=source)
    session.add(f)
    session.add(source)
    session.add(reply)
    session.commit()

    sw = SourceWidget(controller, source)
    sw.set_snippet(source.uuid, f.filename)
    assert sw.preview.text() == f.filename


def test_SourceWidget_set_snippet(mocker, session_maker, session, homedir):
    """
    Snippets are set as expected.
    """
    mock_gui = mocker.MagicMock()
    controller = logic.Controller('http://localhost', mock_gui, session_maker, homedir)
    source = factory.Source(document_count=1)
    f = factory.File(source=source)
    session.add(f)
    session.add(source)
    session.commit()

    sw = SourceWidget(controller, source)
    sw.set_snippet(source.uuid, f.filename)
    assert sw.preview.text() == f.filename

    # check when a different source is specified
    sw.set_snippet("not-the-source-uuid", "something new")
    assert sw.preview.text() == f.filename

    source_uuid = source.uuid
    session.delete(source)
    session.commit()

    # check when the source has been deleted that it catches sqlalchemy.exc.InvalidRequestError
    sw.set_snippet(source_uuid, "something new")


def test_SourceWidget_update_truncate_latest_msg(mocker):
    """
    If the latest message in the conversation is longer than 150 characters,
    truncate and add "..." to the end.
    """
    controller = mocker.MagicMock()
    source = mocker.MagicMock()
    source.journalist_designation = "Testy McTestface"
    source.collection = [factory.Message(content="a" * 151), ]
    sw = SourceWidget(controller, source)

    sw.update()
    assert sw.preview.text().endswith("...")


def test_SourceWidget_delete_source(mocker, session, source):
    mock_delete_source_message_box_object = mocker.MagicMock(DeleteSourceMessageBox)
    mock_controller = mocker.MagicMock()
    mock_delete_source_message = mocker.MagicMock(
        return_value=mock_delete_source_message_box_object)

    sw = SourceWidget(mock_controller, source['source'])

    mocker.patch(
        "securedrop_client.gui.widgets.DeleteSourceMessageBox",
        mock_delete_source_message,
    )

    sw.delete_source(None)
    mock_delete_source_message_box_object.launch.assert_called_with()


def test_SourceWidget_delete_source_when_user_chooses_cancel(mocker, session, source):
    source = source['source']  # to get the Source object
    file_ = factory.File(source=source)
    session.add(file_)
    message = factory.Message(source=source)
    session.add(message)
    session.commit()

    mock_message_box_question = mocker.MagicMock(QMessageBox.question)
    mock_message_box_question.return_value = QMessageBox.Cancel

    mock_controller = mocker.MagicMock()
    sw = SourceWidget(mock_controller, source)

    mocker.patch(
        "securedrop_client.gui.widgets.QMessageBox.question",
        mock_message_box_question,
    )
    sw.delete_source(None)
    sw.controller.delete_source.assert_not_called()


def test_SourceWidget__on_source_deleted(mocker, session, source):
    controller = mocker.MagicMock()
    sw = SourceWidget(controller, factory.Source(uuid='123'))
    sw._on_source_deleted('123')
    assert sw.gutter.isHidden()
    assert sw.metadata.isHidden()
    assert sw.preview.isHidden()
    assert not sw.waiting_delete_confirmation.isHidden()


def test_SourceWidget__on_source_deleted_wrong_uuid(mocker, session, source):
    controller = mocker.MagicMock()
    sw = SourceWidget(controller, factory.Source(uuid='123'))
    sw._on_source_deleted('321')
    assert not sw.gutter.isHidden()
    assert not sw.metadata.isHidden()
    assert not sw.preview.isHidden()
    assert sw.waiting_delete_confirmation.isHidden()


def test_SourceWidget__on_source_deletion_failed(mocker, session, source):
    controller = mocker.MagicMock()
    sw = SourceWidget(controller, factory.Source(uuid='123'))
    sw._on_source_deleted('123')

    sw._on_source_deletion_failed('123')

    assert not sw.gutter.isHidden()
    assert not sw.metadata.isHidden()
    assert not sw.preview.isHidden()
    assert sw.waiting_delete_confirmation.isHidden()


def test_SourceWidget__on_source_deletion_failed_wrong_uuid(mocker, session, source):
    controller = mocker.MagicMock()
    sw = SourceWidget(controller, factory.Source(uuid='123'))
    sw._on_source_deleted('123')

    sw._on_source_deletion_failed('321')

    assert sw.gutter.isHidden()
    assert sw.metadata.isHidden()
    assert sw.preview.isHidden()
    assert not sw.waiting_delete_confirmation.isHidden()


def test_SourceWidget_uses_SecureQLabel(mocker):
    """
    Ensure the source widget preview uses SecureQLabel and is not injectable
    """
    controller = mocker.MagicMock()
    source = mocker.MagicMock()
    source.journalist_designation = "Testy McTestface"
    source.collection = [factory.Message(content="a" * 121), ]
    sw = SourceWidget(controller, source)

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
    stb = StarToggleButton(controller, 'mock_uuid', True)
    stb.pressed = mocker.MagicMock()
    stb.setIcon = mocker.MagicMock()
    stb.set_icon = mocker.MagicMock()
    load_icon_fn = mocker.patch("securedrop_client.gui.widgets.load_icon")

    # Hover enter
    test_event = QEvent(QEvent.HoverEnter)
    stb.eventFilter(stb, test_event)
    assert stb.setIcon.call_count == 1
    load_icon_fn.assert_called_once_with('star_hover.svg')

    # Hover leave
    test_event = QEvent(QEvent.HoverLeave)
    stb.eventFilter(stb, test_event)
    stb.set_icon.assert_called_once_with(on='star_on.svg', off='star_off.svg')

    # Authentication change
    stb.on_authentication_changed(authenticated=True)
    assert stb.isCheckable() is True
    stb.pressed.disconnect.assert_called_once_with()
    stb.pressed.connect.assert_called_once_with(stb.on_pressed)


def test_StarToggleButton_eventFilter_when_not_checked(mocker):
    """
    Ensure the hover events are handled properly when star is checked and online.
    """
    controller = mocker.MagicMock()
    controller.is_authenticated = True
    stb = StarToggleButton(controller, 'mock_uuid', False)
    stb.pressed = mocker.MagicMock()
    stb.setIcon = mocker.MagicMock()
    stb.set_icon = mocker.MagicMock()
    load_icon_fn = mocker.patch("securedrop_client.gui.widgets.load_icon")

    # Hover enter
    test_event = QEvent(QEvent.HoverEnter)
    stb.eventFilter(stb, test_event)
    assert stb.setIcon.call_count == 1
    load_icon_fn.assert_called_once_with('star_hover.svg')

    # Hover leave
    test_event = QEvent(QEvent.HoverLeave)
    stb.eventFilter(stb, test_event)
    stb.set_icon.assert_called_once_with(on='star_on.svg', off='star_off.svg')

    # Authentication change
    stb.on_authentication_changed(authenticated=True)
    assert stb.isCheckable() is True
    stb.pressed.disconnect.assert_called_once_with()
    stb.pressed.connect.assert_called_once_with(stb.on_pressed)


def test_StarToggleButton_eventFilter_when_checked_and_offline(mocker):
    """
    Ensure the hover events do not change the icon when offline and that the star icon is set to
    off='star_on.svg' when checked and offline.
    """
    controller = mocker.MagicMock()
    stb = StarToggleButton(controller, 'mock_uuid', True)
    stb.pressed = mocker.MagicMock()
    stb.setIcon = mocker.MagicMock()
    stb.set_icon = mocker.MagicMock()
    load_icon_fn = mocker.patch("securedrop_client.gui.widgets.load_icon")

    # Authentication change
    stb.on_authentication_changed(authenticated=False)
    assert stb.isCheckable() is False
    stb.set_icon.assert_called_with(on='star_on.svg', off='star_on.svg')
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
    stb = StarToggleButton(controller, 'mock_uuid', False)
    stb.pressed = mocker.MagicMock()
    stb.setIcon = mocker.MagicMock()
    stb.set_icon = mocker.MagicMock()
    load_icon_fn = mocker.patch("securedrop_client.gui.widgets.load_icon")

    # Authentication change
    stb.on_authentication_changed(authenticated=False)
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
    stb = StarToggleButton(controller, 'mock_uuid', True)
    stb.on_pressed = mocker.MagicMock()
    stb.on_authentication_changed(authenticated=True)

    stb.click()

    stb.on_pressed.assert_called_once_with()
    assert stb.isChecked() is False


def test_StarToggleButton_on_authentication_changed_while_authenticated_and_not_checked(mocker):
    """
    If on_authentication_changed is set up correctly, then calling toggle on an unchecked button
    should result in the button being unchecked.
    """
    controller = mocker.MagicMock()
    stb = StarToggleButton(controller, 'mock_uuid', False)
    stb.on_pressed = mocker.MagicMock()
    stb.on_authentication_changed(authenticated=True)

    stb.click()

    stb.on_pressed.assert_called_once_with()
    assert stb.isChecked() is True


def test_StarToggleButton_on_authentication_changed_while_offline_mode_and_not_checked(mocker):
    """
    Ensure on_authentication_changed is set up correctly for offline mode.
    """
    controller = mocker.MagicMock()
    stb = StarToggleButton(controller, 'mock_uuid', False)
    stb.on_pressed_offline = mocker.MagicMock()
    stb.on_pressed = mocker.MagicMock()
    stb.on_authentication_changed(authenticated=False)

    stb.click()

    stb.on_pressed_offline.assert_called_once_with()
    stb.on_pressed.assert_not_called()
    assert stb.isChecked() is False


def test_StarToggleButton_on_authentication_changed_while_offline_mode_and_checked(mocker):
    """
    Ensure on_authentication_changed is set up correctly for offline mode.
    """
    controller = mocker.MagicMock()
    stb = StarToggleButton(controller, 'mock_uuid', True)
    stb.on_pressed_offline = mocker.MagicMock()
    stb.on_pressed = mocker.MagicMock()
    stb.on_authentication_changed(authenticated=False)

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
    stb = StarToggleButton(controller, 'mock_uuid', False)

    stb.click()

    stb.controller.update_star.assert_called_once_with('mock_uuid', False)
    assert stb.isChecked()


def test_StarToggleButton_on_pressed_toggles_to_unstarred(mocker):
    """
    Ensure pressing the star button toggles from starred to unstarred.
    """
    controller = mocker.MagicMock()
    stb = StarToggleButton(controller, 'mock_uuid', True)

    stb.click()

    stb.controller.update_star.assert_called_once_with('mock_uuid', True)
    assert not stb.isChecked()


def test_StarToggleButton_on_pressed_offline(mocker):
    """
    Ensure toggle is disabled when offline.
    """
    controller = mocker.MagicMock()
    controller.is_authenticated = False
    stb = StarToggleButton(controller, 'mock_uuid', True)

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
    set_icon_fn = mocker.patch('securedrop_client.gui.SvgToggleButton.set_icon')

    stb.on_authentication_changed(False)
    assert stb.isCheckable() is False
    set_icon_fn.assert_called_with(on='star_on.svg', off='star_on.svg')

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
    stb = StarToggleButton(controller, 'mock_uuid', True)

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
    '''
    Ensure the button is toggled to the state provided in the failure handler and that the pending
    count is decremented if the source uuid matches.
    '''
    controller = mocker.MagicMock()
    controller.is_authenticated = True
    stb = StarToggleButton(controller, 'mock_uuid', False)

    stb.click()
    assert stb.is_starred is True
    assert stb.pending_count == 1
    stb.on_star_update_failed('mock_uuid', is_starred=False)
    assert stb.is_starred is False
    assert stb.pending_count == 0


def test_StarToggleButton_on_star_update_failed_for_non_matching_source_uuid(mocker):
    '''
    Ensure the button is not toggled and that the pending count stays the same if the source uuid
    does not match.
    '''
    controller = mocker.MagicMock()
    controller.is_authenticated = True
    stb = StarToggleButton(controller, 'mock_uuid', False)

    stb.click()
    assert stb.is_starred is True
    assert stb.pending_count == 1
    stb.on_star_update_failed('some_other_uuid', is_starred=False)
    assert stb.is_starred is True
    assert stb.pending_count == 1


def test_StarToggleButton_on_star_update_successful(mocker):
    '''
    Ensure that the pending count is decremented if the source uuid matches.
    '''
    controller = mocker.MagicMock()
    controller.is_authenticated = True
    stb = StarToggleButton(controller, 'mock_uuid', True)

    stb.click()
    assert stb.pending_count == 1
    stb.on_star_update_successful('mock_uuid')
    assert stb.pending_count == 0


def test_StarToggleButton_on_star_update_successful_for_non_matching_source_uuid(mocker):
    '''
    Ensure that the pending count is not decremented if the source uuid does not match.
    '''
    controller = mocker.MagicMock()
    controller.is_authenticated = True
    stb = StarToggleButton(controller, 'mock_uuid', True)

    stb.click()
    assert stb.pending_count == 1
    stb.on_star_update_successful('some_other_uuid')
    assert stb.pending_count == 1


def test_LoginDialog_setup(mocker, i18n):
    """
    The LoginView is correctly initialised.
    """
    mock_controller = mocker.MagicMock()
    ld = LoginDialog(None)
    ld.offline_mode = mocker.MagicMock()

    ld.setup(mock_controller)

    assert ld.controller == mock_controller
    ld.offline_mode.clicked.connect.assert_called_once_with(ld.controller.login_offline_mode)


def test_LoginDialog_reset(mocker):
    """
    Ensure the state of the login view is returned to the correct state.
    """
    mock_controller = mocker.MagicMock()

    ld = LoginDialog(None)
    ld.setup(mock_controller)
    ld.username_field = mocker.MagicMock()
    ld.password_field = mocker.MagicMock()
    ld.tfa_field = mocker.MagicMock()
    ld.setDisabled = mocker.MagicMock()
    ld.error_bar = mocker.MagicMock()

    ld.reset()

    ld.username_field.setText.assert_called_once_with('')
    ld.password_field.setText.assert_called_once_with('')
    ld.tfa_field.setText.assert_called_once_with('')
    ld.setDisabled.assert_called_once_with(False)
    ld.error_bar.clear_message.assert_called_once_with()


def test_LoginDialog_error(mocker, i18n):
    """
    Any error message passed in is assigned as the text for the error label.
    """
    mock_controller = mocker.MagicMock()
    ld = LoginDialog(None)
    ld.setup(mock_controller)
    ld.error_bar = mocker.MagicMock()
    ld.error('foo')
    ld.error_bar.set_message.assert_called_once_with('foo')


def test_LoginDialog_validate_no_input(mocker):
    """
    If the user doesn't provide input, tell them and give guidance.
    """
    mock_controller = mocker.MagicMock()

    ld = LoginDialog(None)
    ld.setup(mock_controller)
    ld.username_field.text = mocker.MagicMock(return_value='')
    ld.password_field.text = mocker.MagicMock(return_value='')
    ld.tfa_field.text = mocker.MagicMock(return_value='')
    ld.setDisabled = mocker.MagicMock()
    ld.error = mocker.MagicMock()

    ld.validate()

    assert ld.setDisabled.call_count == 2
    assert ld.error.call_count == 1


def test_LoginDialog_validate_input_non_numeric_2fa(mocker):
    """
    If the user doesn't provide numeric 2fa input, tell them and give
    guidance.
    """
    mock_controller = mocker.MagicMock()

    ld = LoginDialog(None)
    ld.setup(mock_controller)
    ld.username_field.text = mocker.MagicMock(return_value='foo')
    ld.password_field.text = mocker.MagicMock(return_value='nicelongpassword')
    ld.tfa_field.text = mocker.MagicMock(return_value='baz')
    ld.setDisabled = mocker.MagicMock()
    ld.error = mocker.MagicMock()

    ld.validate()

    assert ld.setDisabled.call_count == 2
    assert ld.error.call_count == 1
    assert mock_controller.login.call_count == 0


def test_LoginDialog_validate_too_short_username(mocker):
    """
    If the username is too small, we show an informative error message.
    """
    mock_controller = mocker.MagicMock()

    ld = LoginDialog(None)
    ld.setup(mock_controller)
    ld.username_field.text = mocker.MagicMock(return_value='he')
    ld.password_field.text = mocker.MagicMock(return_value='nicelongpassword')
    ld.tfa_field.text = mocker.MagicMock(return_value='123456')
    ld.setDisabled = mocker.MagicMock()
    ld.error = mocker.MagicMock()

    ld.validate()

    assert ld.setDisabled.call_count == 2
    assert ld.error.call_count == 1
    assert mock_controller.login.call_count == 0


def test_LoginDialog_validate_too_short_password(mocker):
    """
    If the password is too small, we show an informative error message.
    """
    mock_controller = mocker.MagicMock()

    ld = LoginDialog(None)
    ld.setup(mock_controller)
    ld.username_field.text = mocker.MagicMock(return_value='foo')
    ld.password_field.text = mocker.MagicMock(return_value='bar')
    ld.tfa_field.text = mocker.MagicMock(return_value='123456')
    ld.setDisabled = mocker.MagicMock()
    ld.error = mocker.MagicMock()

    ld.validate()

    assert ld.setDisabled.call_count == 2
    assert ld.error.call_count == 1
    assert mock_controller.login.call_count == 0


def test_LoginDialog_validate_too_long_password(mocker):
    """
    If the password is too long, we show an informative error message.
    """
    mock_controller = mocker.MagicMock()
    ld = LoginDialog(None)
    ld.setup(mock_controller)

    max_password_len = 128
    too_long_password = 'a' * (max_password_len + 1)

    ld.username_field.text = mocker.MagicMock(return_value='foo')
    ld.password_field.text = mocker.MagicMock(return_value=too_long_password)
    ld.tfa_field.text = mocker.MagicMock(return_value='123456')
    ld.setDisabled = mocker.MagicMock()
    ld.error = mocker.MagicMock()

    ld.validate()

    assert ld.setDisabled.call_count == 2
    assert ld.error.call_count == 1
    assert mock_controller.login.call_count == 0


def test_LoginDialog_validate_input_ok(mocker):
    """
    Valid input from the user causes a call to the controller's login method.
    """
    mock_controller = mocker.MagicMock()

    ld = LoginDialog(None)
    ld.setup(mock_controller)
    ld.username_field.text = mocker.MagicMock(return_value='foo')
    ld.password_field.text = mocker.MagicMock(return_value='nicelongpassword')
    ld.tfa_field.text = mocker.MagicMock(return_value='123456')
    ld.setDisabled = mocker.MagicMock()
    ld.error = mocker.MagicMock()

    ld.validate()

    assert ld.setDisabled.call_count == 1
    assert ld.error.call_count == 0
    mock_controller.login.assert_called_once_with('foo', 'nicelongpassword', '123456')


def test_LoginDialog_escapeKeyPressEvent(mocker):
    """
    Ensure we don't hide the login dialog when Esc key is pressed.
    """
    ld = LoginDialog(None)
    event = mocker.MagicMock()
    event.key = mocker.MagicMock(return_value=Qt.Key_Escape)

    ld.keyPressEvent(event)

    event.ignore.assert_called_once_with()


@pytest.mark.parametrize("qt_key", [Qt.Key_Enter, Qt.Key_Return])
def test_LoginDialog_submitKeyPressEvent(mocker, qt_key):
    """
    Ensure we submit the form when the user presses [Enter] or [Return]
    """

    ld = LoginDialog(None)
    event = mocker.MagicMock()
    event.key = mocker.MagicMock(return_value=qt_key)

    ld.validate = mocker.MagicMock()

    ld.keyPressEvent(event)

    ld.validate.assert_called_once_with()


def test_LoginDialog_closeEvent_exits(mocker):
    """
    If the main window is not visible, then exit the application when the LoginDialog receives a
    close event.
    """
    mw = QMainWindow()
    ld = LoginDialog(mw)
    sys_exit_fn = mocker.patch('securedrop_client.gui.widgets.sys.exit')
    mw.hide()

    ld.closeEvent(event='mock')

    sys_exit_fn.assert_called_once_with(0)


def test_LoginErrorBar_set_message(mocker):
    error_bar = LoginErrorBar()
    error_bar.error_status_bar = mocker.MagicMock()
    mocker.patch.object(error_bar, 'show')

    error_bar.set_message('mock error')

    error_bar.error_status_bar.setText.assert_called_with('mock error')
    error_bar.show.assert_called_with()


def test_LoginErrorBar_clear_message(mocker):
    error_bar = LoginErrorBar()
    error_bar.error_status_bar = mocker.MagicMock()
    mocker.patch.object(error_bar, 'hide')

    error_bar.clear_message()

    error_bar.error_status_bar.setText.assert_called_with('')
    error_bar.hide.assert_called_with()


def test_LoginOfflineLink(mocker):
    """
    Assert that the clicked signal is emitted on mouse release event.
    """
    offline_link = LoginOfflineLink()
    offline_link.clicked = mocker.MagicMock()

    offline_link.mouseReleaseEvent(None)

    offline_link.clicked.emit.assert_called_with()


def test_LoginDialog_closeEvent_does_not_exit_when_main_window_is_visible(mocker):
    """
    If the main window is visible, then to not exit the application when the LoginDialog receives a
    close event.
    """
    mw = QMainWindow()
    ld = LoginDialog(mw)
    sys_exit_fn = mocker.patch('securedrop_client.gui.widgets.sys.exit')
    mw.show()

    ld.closeEvent(event='mock')

    assert sys_exit_fn.called is False


def test_SpeechBubble_init(mocker):
    """
    Check the speech bubble is configured correctly (there's a label containing
    the passed in text).
    """
    mock_update_signal = mocker.Mock()
    mock_update_connect = mocker.Mock()
    mock_update_signal.connect = mock_update_connect

    mock_download_error_signal = mocker.Mock()
    mock_download_error_connect = mocker.Mock()
    mock_download_error_signal.connect = mock_download_error_connect

    sb = SpeechBubble('mock id', 'hello', mock_update_signal, mock_download_error_signal, 0)

    sb.message.text() == 'hello'
    assert mock_update_connect.called
    assert mock_download_error_connect.called
    assert 'background-color: #102781;' in sb.color_bar.styleSheet()
    assert 'background-color: #fff;' in sb.speech_bubble.styleSheet()


def test_SpeechBubble_init_with_error(mocker):
    """
    Check the speech bubble is configured correctly when error=True.
    """
    mock_update_signal = mocker.Mock()
    mock_update_connect = mocker.Mock()
    mock_update_signal.connect = mock_update_connect

    mock_download_error_signal = mocker.Mock()
    mock_download_error_connect = mocker.Mock()
    mock_download_error_signal.connect = mock_download_error_connect

    sb = SpeechBubble(
        'mock id', 'hello', mock_update_signal, mock_download_error_signal, 0, error=True
    )

    sb.message.text() == 'hello'
    assert mock_update_connect.called
    assert mock_download_error_connect.called
    assert 'background-color: #BCBFCD;' in sb.color_bar.styleSheet()
    assert 'background-color: rgba(255, 255, 255, 0.6);' in sb.message.styleSheet()
    assert 'font-style: italic;' in sb.message.styleSheet()


def test_SpeechBubble_update_text(mocker):
    """
    Check that the calling the slot updates the text.
    """
    mock_signal = mocker.MagicMock()

    msg_id = 'abc123'
    sb = SpeechBubble(msg_id, 'hello', mock_signal, mock_signal, 0)

    new_msg = 'new message'
    sb._update_text('mock_source_uuid', msg_id, new_msg)
    assert sb.message.text() == new_msg

    newer_msg = 'an even newer message'
    sb._update_text('mock_source_uuid', msg_id + 'xxxxx', newer_msg)
    assert sb.message.text() == new_msg


def test_SpeechBubble_html_init(mocker):
    """
    Check the speech bubble is configured correctly (there's a label containing
    the passed in text, with HTML escaped properly).
    """
    mock_signal = mocker.MagicMock()

    bubble = SpeechBubble('mock id', '<b>hello</b>', mock_signal, mock_signal, 0)
    assert bubble.message.text() == '<b>hello</b>'


def test_SpeechBubble_with_apostrophe_in_text(mocker):
    """Check Speech Bubble is displaying text with apostrophe correctly."""
    mock_signal = mocker.MagicMock()

    message = "I'm sure, you are reading my message."
    bubble = SpeechBubble('mock id', message, mock_signal, mock_signal, 0)
    assert bubble.message.text() == message


def test_SpeechBubble_set_error(mocker):
    mock_signal = mocker.MagicMock()

    message_uuid = "mock id"
    message = "I'm sure, you are reading my message."
    bubble = SpeechBubble(message_uuid, message, mock_signal, mock_signal, 0)
    assert bubble.message.text() == message

    error_message = "Oh no."
    bubble.set_error("source id", message_uuid, error_message)
    assert bubble.message.text() == error_message
    assert "font-style: italic;" in bubble.message.styleSheet()
    assert "background-color: rgba(255, 255, 255, 0.6);" in bubble.message.styleSheet()
    assert "background-color: #BCBFCD;" in bubble.color_bar.styleSheet()


def test_MessageWidget_init(mocker):
    """
    Check the CSS is set as expected.
    """
    mock_signal = mocker.Mock()
    mock_connected = mocker.Mock()
    mock_signal.connect = mock_connected

    MessageWidget('mock id', 'hello', mock_signal, mock_signal, 0)

    assert mock_connected.called


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

    ReplyWidget(
        'mock id',
        'hello',
        'dummy',
        mock_update_signal,
        mock_download_failure_signal,
        mock_success_signal,
        mock_failure_signal,
        0,
    )

    assert mock_update_connected.called
    assert mock_success_connected.called
    assert mock_failure_connected.called


def test_ReplyWidget_init_with_error(mocker):
    """
    Check the CSS is set as expected when error=True.
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

    rw = ReplyWidget(
        'mock id',
        'hello',
        'dummy',
        mock_update_signal,
        mock_download_failure_signal,
        mock_success_signal,
        mock_failure_signal,
        0,
        error=True
    )

    assert mock_update_connected.called
    assert mock_success_connected.called
    assert mock_failure_connected.called

    assert "font-style: italic;" in rw.message.styleSheet()
    assert "background-color: rgba(255, 255, 255, 0.6);" in rw.message.styleSheet()
    assert "background-color: #BCBFCD;" in rw.color_bar.styleSheet()


def test_FileWidget_init_file_not_downloaded(mocker, source, session):
    """
    Check the FileWidget is configured correctly when the file is not downloaded.
    """
    file = factory.File(source=source['source'], is_downloaded=False, is_decrypted=None)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget('mock', controller, mocker.MagicMock(), mocker.MagicMock(), 0)

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
    file = factory.File(source=source['source'], is_downloaded=True)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget('mock', controller, mocker.MagicMock(), mocker.MagicMock(), 0)

    assert fw.controller == controller
    assert fw.file.is_downloaded is True
    assert fw.download_button.isHidden()
    assert fw.no_file_name.isHidden()
    assert not fw.export_button.isHidden()
    assert not fw.middot.isHidden()
    assert not fw.print_button.isHidden()
    assert not fw.file_name.isHidden()


def test_FileWidget__set_file_state_under_mouse(mocker, source, session):
    """
    If the download_button is under the mouse, it should show the "hover"
    version of the download_file icon.
    """
    file_ = factory.File(source=source['source'],
                         is_downloaded=False,
                         is_decrypted=None)
    session.add(file_)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file_)
    mock_controller = mocker.MagicMock(get_file=mock_get_file)

    fw = FileWidget(file_.uuid, mock_controller, mocker.MagicMock(), mocker.MagicMock(), 0)
    fw.download_button.underMouse = mocker.MagicMock(return_value=True)
    fw.download_button.setIcon = mocker.MagicMock()
    mock_load = mocker.MagicMock()
    with mocker.patch("securedrop_client.gui.widgets.load_icon", mock_load):
        fw._set_file_state()
        mock_load.assert_called_once_with("download_file_hover.svg")


def test_FileWidget_event_handler_left_click(mocker, session, source):
    """
    Left click on filename should trigger an open.
    """
    file_ = factory.File(source=source['source'],
                         is_downloaded=False,
                         is_decrypted=None)
    session.add(file_)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file_)
    mock_controller = mocker.MagicMock(get_file=mock_get_file)
    test_event = QEvent(QEvent.MouseButtonPress)
    test_event.button = mocker.MagicMock(return_value=Qt.LeftButton)

    fw = FileWidget(file_.uuid, mock_controller, mocker.MagicMock(), mocker.MagicMock(), 0)
    fw._on_left_click = mocker.MagicMock()

    fw.eventFilter(fw, test_event)
    fw._on_left_click.call_count == 1


def test_FileWidget_event_handler_hover(mocker, session, source):
    """
    Hover events when the file isn't being downloaded should change the
    widget's icon.
    """
    file_ = factory.File(source=source['source'],
                         is_downloaded=False,
                         is_decrypted=None)
    session.add(file_)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file_)
    mock_controller = mocker.MagicMock(get_file=mock_get_file)

    fw = FileWidget(file_.uuid, mock_controller, mocker.MagicMock(), mocker.MagicMock(), 0)
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
    file_ = factory.File(source=source['source'],
                         is_downloaded=False,
                         is_decrypted=None)
    session.add(file_)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file_)
    mock_controller = mocker.MagicMock(get_file=mock_get_file)

    fw = FileWidget(file_.uuid, mock_controller, mocker.MagicMock(), mocker.MagicMock(), 0)
    fw.download_button = mocker.MagicMock()
    mock_get_file.assert_called_once_with(file_.uuid)
    mock_get_file.reset_mock()

    fw._on_left_click()
    mock_get_file.assert_called_once_with(file_.uuid)
    mock_controller.on_submission_download.assert_called_once_with(
        db.File, file_.uuid)


def test_FileWidget_on_left_click_downloading_in_progress(mocker, session, source):
    """
    Left click on download when file is not downloaded but is in progress
    downloading should not trigger a download.
    """
    file_ = factory.File(source=source['source'],
                         is_downloaded=False,
                         is_decrypted=None)
    session.add(file_)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file_)
    mock_controller = mocker.MagicMock(get_file=mock_get_file)

    fw = FileWidget(file_.uuid, mock_controller, mocker.MagicMock(), mocker.MagicMock(), 0)
    fw.downloading = True
    fw.download_button = mocker.MagicMock()
    mock_get_file.assert_called_once_with(file_.uuid)
    mock_get_file.reset_mock()

    fw._on_left_click()
    mock_get_file.call_count == 0
    mock_controller.on_submission_download.call_count == 0


def test_FileWidget_start_button_animation(mocker, session, source):
    """
    Ensure widget state is updated when this method is called.
    """
    file_ = factory.File(source=source['source'],
                         is_downloaded=False,
                         is_decrypted=None)
    session.add(file_)
    session.commit()
    mock_get_file = mocker.MagicMock(return_value=file_)
    mock_controller = mocker.MagicMock(get_file=mock_get_file)
    fw = FileWidget(file_.uuid, mock_controller, mocker.MagicMock(), mocker.MagicMock(), 0)
    fw.download_button = mocker.MagicMock()
    fw.start_button_animation()
    # Check indicators of activity have been updated.
    assert fw.download_button.setIcon.call_count == 1
    fw.download_button.setText.assert_called_once_with(" DOWNLOADING ")
    fw.download_button.setStyleSheet.assert_called_once_with("color: #05a6fe")


def test_FileWidget_on_left_click_open(mocker, session, source):
    """
    Left click on open when file is downloaded should trigger an open.
    """
    file_ = factory.File(source=source['source'], is_downloaded=True)
    session.add(file_)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file_)
    mock_controller = mocker.MagicMock(get_file=mock_get_file)

    fw = FileWidget(file_.uuid, mock_controller, mocker.MagicMock(), mocker.MagicMock(), 0)
    fw._on_left_click()
    fw.controller.on_file_open.assert_called_once_with(file_)


def test_FileWidget_set_button_animation_frame(mocker, session, source):
    """
    Left click on download when file is not downloaded should trigger
    a download.
    """
    file_ = factory.File(source=source['source'],
                         is_downloaded=False,
                         is_decrypted=None)
    session.add(file_)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file_)
    mock_controller = mocker.MagicMock(get_file=mock_get_file)

    fw = FileWidget(file_.uuid, mock_controller, mocker.MagicMock(), mocker.MagicMock(), 0)
    fw.download_button = mocker.MagicMock()
    fw.set_button_animation_frame(1)
    assert fw.download_button.setIcon.call_count == 1


def test_FileWidget_update(mocker, session, source):
    """
    The update method should show/hide widgets if file is downloaded
    """
    file = factory.File(source=source['source'], is_downloaded=True)
    session.add(file)
    session.commit()
    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)
    fw = FileWidget(file.uuid, controller, mocker.MagicMock(), mocker.MagicMock(), 0)

    fw.update()

    assert fw.download_button.isHidden()
    assert fw.no_file_name.isHidden()
    assert not fw.file_name.isHidden()


def test_FileWidget_on_file_download_updates_items_when_uuid_matches(mocker, source, session):
    """
    The _on_file_download method should update the FileWidget
    """
    file = factory.File(source=source['source'], is_downloaded=True)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(file.uuid, controller, mocker.MagicMock(), mocker.MagicMock(), 0)
    fw.update = mocker.MagicMock()

    fw._on_file_downloaded(file.source.uuid, file.uuid, str(file))

    assert fw.download_button.isHidden()
    assert not fw.export_button.isHidden()
    assert not fw.middot.isHidden()
    assert not fw.print_button.isHidden()
    assert fw.no_file_name.isHidden()
    assert not fw.file_name.isHidden()


def test_FileWidget_filename_truncation(mocker, source, session):
    """
    FileWidget should truncate long filenames.

    The full filename should be available in the tooltip.
    """
    filename = "1-{}".format("x" * 1000)
    file = factory.File(source=source['source'], filename=filename)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(file.uuid, controller, mocker.MagicMock(), mocker.MagicMock(), 0)
    fw.update = mocker.MagicMock()

    fw._on_file_downloaded(file.source.uuid, file.uuid, str(file))

    assert fw.file_name.text().endswith("...")
    assert fw.file_name.toolTip() == filename


def test_FileWidget_on_file_download_updates_items_when_uuid_does_not_match(
    mocker, homedir, session, source,
):
    """
    The _on_file_download method should clear and update the FileWidget
    """
    file = factory.File(source=source['source'], is_downloaded=True)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(file.uuid, controller, mocker.MagicMock(), mocker.MagicMock(), 0)
    fw.clear = mocker.MagicMock()
    fw.update = mocker.MagicMock()

    fw._on_file_downloaded('not a matching source uuid', 'not a matching file uuid', 'mock')

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
    file = factory.File(source=source['source'], is_decrypted=None, is_downloaded=False)
    session.add(file)
    session.commit()

    mock_gui = mocker.MagicMock()
    controller = logic.Controller('http://localhost', mock_gui, session_maker, homedir)

    fw = FileWidget(
        file.uuid,
        controller,
        controller.file_ready,
        controller.file_missing,
        0
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
    mocker, homedir, session, source,
):
    """
    The _on_file_missing method should not update the FileWidget when uuid doesn't match.
    """
    file = factory.File(source=source['source'])
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(file.uuid, controller, mocker.MagicMock(), mocker.MagicMock(), 0)
    fw.download_button.show = mocker.MagicMock()

    fw._on_file_missing('not a matching source uuid', 'not a matching file uuid', 'mock filename')

    fw.download_button.show.assert_not_called()


def test_FileWidget__on_export_clicked(mocker, session, source):
    """
    Ensure preflight checks start when the EXPORT button is clicked and that password is requested
    """
    file = factory.File(source=source['source'], is_downloaded=True)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(file.uuid, controller, mocker.MagicMock(), mocker.MagicMock(), 0)
    fw.update = mocker.MagicMock()
    mocker.patch('securedrop_client.gui.widgets.QDialog.exec')
    controller.run_export_preflight_checks = mocker.MagicMock()
    controller.downloaded_file_exists = mocker.MagicMock(return_value=True)

    dialog = mocker.patch('securedrop_client.gui.widgets.ExportDialog')

    fw._on_export_clicked()
    dialog.assert_called_once_with(controller, file.uuid, file.filename)


def test_FileWidget__on_export_clicked_missing_file(mocker, session, source):
    """
    Ensure dialog does not open when the EXPORT button is clicked yet the file to export is missing
    """
    file = factory.File(source=source['source'], is_downloaded=True)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(file.uuid, controller, mocker.MagicMock(), mocker.MagicMock(), 0)
    fw.update = mocker.MagicMock()
    mocker.patch('securedrop_client.gui.widgets.QDialog.exec')
    controller.run_export_preflight_checks = mocker.MagicMock()
    controller.downloaded_file_exists = mocker.MagicMock(return_value=False)
    dialog = mocker.patch('securedrop_client.gui.widgets.ExportDialog')

    fw._on_export_clicked()

    controller.run_export_preflight_checks.assert_not_called()
    dialog.assert_not_called()


def test_FileWidget__on_print_clicked(mocker, session, source):
    """
    Ensure print_file is called when the PRINT button is clicked
    """
    file = factory.File(source=source['source'], is_downloaded=True)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(file.uuid, controller, mocker.MagicMock(), mocker.MagicMock(), 0)
    fw.update = mocker.MagicMock()
    mocker.patch('securedrop_client.gui.widgets.QDialog.exec')
    controller.print_file = mocker.MagicMock()
    controller.downloaded_file_exists = mocker.MagicMock(return_value=True)

    dialog = mocker.patch('securedrop_client.gui.widgets.PrintDialog')

    fw._on_print_clicked()

    dialog.assert_called_once_with(controller, file.uuid, file.filename)


def test_FileWidget__on_print_clicked_missing_file(mocker, session, source):
    """
    Ensure dialog does not open when the EXPORT button is clicked yet the file to export is missing
    """
    file = factory.File(source=source['source'], is_downloaded=True)
    session.add(file)
    session.commit()

    get_file = mocker.MagicMock(return_value=file)
    controller = mocker.MagicMock(get_file=get_file)

    fw = FileWidget(file.uuid, controller, mocker.MagicMock(), mocker.MagicMock(), 0)
    fw.update = mocker.MagicMock()
    mocker.patch('securedrop_client.gui.widgets.QDialog.exec')
    controller.print_file = mocker.MagicMock()
    controller.downloaded_file_exists = mocker.MagicMock(return_value=False)
    dialog = mocker.patch('securedrop_client.gui.widgets.PrintDialog')

    fw._on_print_clicked()

    controller.print_file.assert_not_called()
    dialog.assert_not_called()


def test_FileWidget_update_file_size_with_deleted_file(
    mocker, homedir, config, session_maker, source
):
    mock_gui = mocker.MagicMock()
    controller = logic.Controller('http://localhost', mock_gui, session_maker, homedir)

    file = factory.File(source=source['source'], is_downloaded=True)
    controller.session.add(file)
    controller.session.commit()

    fw = FileWidget(file.uuid, controller, mocker.MagicMock(), mocker.MagicMock(), 0)

    with mocker.patch(
        "securedrop_client.gui.widgets.humanize_filesize",
        side_effect=Exception("boom!")
    ):
        fw.update_file_size()
        assert fw.file_size.text() == ""


@pytest.mark.parametrize("key", [Qt.Key_Enter, Qt.Key_Return])
def test_ModalDialog_keyPressEvent_does_not_close_on_enter_or_return(mocker, key):
    dialog = ModalDialog()
    dialog.close = mocker.MagicMock()

    event = QKeyEvent(QEvent.KeyPress, key, Qt.NoModifier)
    dialog.keyPressEvent(event)

    dialog.close.assert_not_called()


@pytest.mark.parametrize("key", [Qt.Key_Enter, Qt.Key_Return])
def test_ModalDialog_keyPressEvent_cancel_on_enter_when_focused(mocker, key):
    dialog = ModalDialog()
    dialog.cancel_button.click = mocker.MagicMock()
    dialog.cancel_button.hasFocus = mocker.MagicMock(return_value=True)

    event = QKeyEvent(QEvent.KeyPress, key, Qt.NoModifier)
    dialog.keyPressEvent(event)

    dialog.cancel_button.click.assert_called_once_with()


@pytest.mark.parametrize("key", [Qt.Key_Enter, Qt.Key_Return])
def test_ModalDialog_keyPressEvent_continue_on_enter(mocker, key):
    dialog = ModalDialog()
    dialog.continue_button.click = mocker.MagicMock()

    event = QKeyEvent(QEvent.KeyPress, key, Qt.NoModifier)
    dialog.keyPressEvent(event)

    dialog.continue_button.click.assert_called_once_with()


@pytest.mark.parametrize("key", [Qt.Key_Alt, Qt.Key_A])
def test_ModalDialog_keyPressEvent_does_not_close_for_other_keys(mocker, key):
    dialog = ModalDialog()
    dialog.close = mocker.MagicMock()

    event = QKeyEvent(QEvent.KeyPress, key, Qt.NoModifier)
    dialog.keyPressEvent(event)

    dialog.close.assert_not_called()


def test_ModalDialog_animation_of_activestate(mocker):
    dialog = ModalDialog()
    assert dialog.button_animation
    dialog.button_animation.start = mocker.MagicMock()
    dialog.button_animation.stop = mocker.MagicMock()
    dialog.continue_button = mocker.MagicMock()

    # Check the animation frame is updated as expected.
    dialog.animate_activestate()
    assert dialog.continue_button.setIcon.call_count == 1
    dialog.continue_button.reset_mock()

    # Check starting the animated state works as expected.
    dialog.start_animate_activestate()
    dialog.button_animation.start.assert_called_once_with()
    dialog.continue_button.setText.assert_called_once_with("")
    assert dialog.continue_button.setMinimumSize.call_count == 1
    assert dialog.continue_button.setStyleSheet.call_count == 1

    dialog.continue_button.reset_mock()

    # Check stopping the animated state works as expected.
    dialog.stop_animate_activestate()
    dialog.button_animation.stop.assert_called_once_with()
    dialog.continue_button.setText.assert_called_once_with("CONTINUE")
    assert dialog.continue_button.setIcon.call_count == 1
    assert dialog.continue_button.setStyleSheet.call_count == 1


def test_ModalDialog_animation_of_header(mocker):
    dialog = ModalDialog()
    assert dialog.header_animation
    dialog.header_animation.start = mocker.MagicMock()
    dialog.header_animation.stop = mocker.MagicMock()
    dialog.header_icon.setVisible = mocker.MagicMock()
    dialog.header_spinner_label.setVisible = mocker.MagicMock()
    dialog.header_spinner_label.setPixmap = mocker.MagicMock()

    # Check the animation frame is updated as expected.
    dialog.animate_header()
    assert dialog.header_spinner_label.setPixmap.call_count == 1

    # Check starting the animated state works as expected.
    dialog.start_animate_header()
    dialog.header_animation.start.assert_called_once_with()
    dialog.header_icon.setVisible.assert_called_once_with(False)
    dialog.header_spinner_label.setVisible.assert_called_once_with(True)

    dialog.header_icon.setVisible.reset_mock()
    dialog.header_spinner_label.setVisible.reset_mock()

    # Check stopping the animated state works as expected.
    dialog.stop_animate_header()
    dialog.header_animation.stop.assert_called_once_with()
    dialog.header_icon.setVisible.assert_called_once_with(True)
    dialog.header_spinner_label.setVisible.assert_called_once_with(False)


def test_ExportDialog_init(mocker):
    _show_starting_instructions_fn = mocker.patch(
        'securedrop_client.gui.widgets.ExportDialog._show_starting_instructions')

    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')

    _show_starting_instructions_fn.assert_called_once_with()
    assert dialog.passphrase_form.isHidden()


def test_ExportDialog_init_sanitizes_filename(mocker):
    secure_qlabel = mocker.patch('securedrop_client.gui.widgets.SecureQLabel')
    mocker.patch('securedrop_client.gui.widgets.QVBoxLayout.addWidget')
    filename = '<script>alert("boom!");</script>'

    ExportDialog(mocker.MagicMock(), 'mock_uuid', filename)

    secure_qlabel.call_args_list[1].assert_called_with(filename)


def test_ExportDialog__show_starting_instructions(mocker):
    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')

    dialog._show_starting_instructions()

    assert dialog.header.text() == \
        'Preparing to export:' \
        '<br />' \
        '<span style="font-weight:normal">mock.jpg</span>'
    assert dialog.body.text() == \
        '<h2>Understand the risks before exporting files</h2>' \
        '<b>Malware</b>' \
        '<br />' \
        'This workstation lets you open files securely. If you open files on another ' \
        'computer, any embedded malware may spread to your computer or network. If you are ' \
        'unsure how to manage this risk, please print the file, or contact your ' \
        'administrator.' \
        '<br /><br />' \
        '<b>Anonymity</b>' \
        '<br />' \
        'Files submitted by sources may contain information or hidden metadata that ' \
        'identifies who they are. To protect your sources, please consider redacting files ' \
        'before working with them on network-connected computers.'
    assert not dialog.header.isHidden()
    assert not dialog.header_line.isHidden()
    assert dialog.error_details.isHidden()
    assert not dialog.body.isHidden()
    assert dialog.passphrase_form.isHidden()
    assert not dialog.continue_button.isHidden()
    assert not dialog.cancel_button.isHidden()


def test_ExportDialog___show_passphrase_request_message(mocker):
    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')

    dialog._show_passphrase_request_message()

    assert dialog.header.text() == 'Enter passphrase for USB drive'
    assert not dialog.header.isHidden()
    assert dialog.header_line.isHidden()
    assert dialog.error_details.isHidden()
    assert dialog.body.isHidden()
    assert not dialog.passphrase_form.isHidden()
    assert not dialog.continue_button.isHidden()
    assert not dialog.cancel_button.isHidden()


def test_ExportDialog__show_passphrase_request_message_again(mocker):
    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')

    dialog._show_passphrase_request_message_again()

    assert dialog.header.text() == 'Enter passphrase for USB drive'
    assert dialog.error_details.text() == 'The passphrase provided did not work. Please try again.'
    assert dialog.body.isHidden()
    assert not dialog.header.isHidden()
    assert dialog.header_line.isHidden()
    assert not dialog.error_details.isHidden()
    assert dialog.body.isHidden()
    assert not dialog.passphrase_form.isHidden()
    assert not dialog.continue_button.isHidden()
    assert not dialog.cancel_button.isHidden()


def test_ExportDialog__show_success_message(mocker):
    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')

    dialog._show_success_message()

    assert dialog.header.text() == 'Export successful'
    assert dialog.body.text() == \
        'Remember to be careful when working with files outside of your Workstation machine.'
    assert not dialog.header.isHidden()
    assert not dialog.header_line.isHidden()
    assert dialog.error_details.isHidden()
    assert not dialog.body.isHidden()
    assert dialog.passphrase_form.isHidden()
    assert not dialog.continue_button.isHidden()
    assert dialog.cancel_button.isHidden()


def test_ExportDialog__show_insert_usb_message(mocker):
    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')

    dialog._show_insert_usb_message()

    assert dialog.header.text() == 'Insert encrypted USB drive'
    assert dialog.body.text() == \
        'Please insert one of the export drives provisioned specifically ' \
        'for the SecureDrop Workstation.'
    assert not dialog.header.isHidden()
    assert not dialog.header_line.isHidden()
    assert dialog.error_details.isHidden()
    assert not dialog.body.isHidden()
    assert dialog.passphrase_form.isHidden()
    assert not dialog.continue_button.isHidden()
    assert not dialog.cancel_button.isHidden()


def test_ExportDialog__show_insert_encrypted_usb_message(mocker):
    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')

    dialog._show_insert_encrypted_usb_message()

    assert dialog.header.text() == 'Insert encrypted USB drive'
    assert dialog.error_details.text() == \
        'Either the drive is not encrypted or there is something else wrong with it.'
    assert dialog.body.text() == \
        'Please insert one of the export drives provisioned specifically for the SecureDrop ' \
        'Workstation.'
    assert not dialog.header.isHidden()
    assert not dialog.header_line.isHidden()
    assert not dialog.error_details.isHidden()
    assert not dialog.body.isHidden()
    assert dialog.passphrase_form.isHidden()
    assert not dialog.continue_button.isHidden()
    assert not dialog.cancel_button.isHidden()


def test_ExportDialog__show_generic_error_message(mocker):
    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')
    dialog.error_status = 'mock_error_status'

    dialog._show_generic_error_message()

    assert dialog.header.text() == 'Export failed'
    assert dialog.body.text() == 'mock_error_status: See your administrator for help.'
    assert not dialog.header.isHidden()
    assert not dialog.header_line.isHidden()
    assert dialog.error_details.isHidden()
    assert not dialog.body.isHidden()
    assert dialog.passphrase_form.isHidden()
    assert not dialog.continue_button.isHidden()
    assert not dialog.cancel_button.isHidden()


def test_ExportDialog__export_file(mocker):
    controller = mocker.MagicMock()
    controller.export_file_to_usb_drive = mocker.MagicMock()
    dialog = ExportDialog(controller, 'mock_uuid', 'mock.jpg')
    dialog.passphrase_field.text = mocker.MagicMock(return_value='mock_passphrase')

    dialog._export_file()

    controller.export_file_to_usb_drive.assert_called_once_with('mock_uuid', 'mock_passphrase')


def test_ExportDialog__on_preflight_success(mocker):
    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')
    dialog._show_passphrase_request_message = mocker.MagicMock()
    dialog.continue_button = mocker.MagicMock()
    dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=False)

    dialog._on_preflight_success()

    dialog._show_passphrase_request_message.assert_not_called()
    dialog.continue_button.clicked.connect.assert_called_once_with(
        dialog._show_passphrase_request_message)


def test_ExportDialog__on_preflight_success_when_continue_enabled(mocker):
    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')
    dialog._show_passphrase_request_message = mocker.MagicMock()
    dialog.continue_button.setEnabled(True)

    dialog._on_preflight_success()

    dialog._show_passphrase_request_message.assert_called_once_with()


def test_ExportDialog__on_preflight_success_enabled_after_preflight_success(mocker):
    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')
    assert not dialog.continue_button.isEnabled()
    dialog._on_preflight_success()
    assert dialog.continue_button.isEnabled()


def test_ExportDialog__on_preflight_success_enabled_after_preflight_failure(mocker):
    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')
    assert not dialog.continue_button.isEnabled()
    dialog._on_preflight_failure(mocker.MagicMock())
    assert dialog.continue_button.isEnabled()


def test_ExportDialog__on_preflight_failure(mocker):
    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')
    dialog._update_dialog = mocker.MagicMock()

    error = ExportError('mock_error_status')
    dialog._on_preflight_failure(error)

    dialog._update_dialog.assert_called_with('mock_error_status')


def test_ExportDialog__on_export_success(mocker):
    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')
    dialog._show_success_message = mocker.MagicMock()

    dialog._on_export_success()

    dialog._show_success_message.assert_called_once_with()


def test_ExportDialog__on_export_failure(mocker):
    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')
    dialog._update_dialog = mocker.MagicMock()

    error = ExportError('mock_error_status')
    dialog._on_export_failure(error)

    dialog._update_dialog.assert_called_with('mock_error_status')


def test_ExportDialog__update_dialog_when_status_is_USB_NOT_CONNECTED(mocker):
    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock_filename')
    dialog._show_insert_usb_message = mocker.MagicMock()
    dialog.continue_button = mocker.MagicMock()
    dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    dialog._update_dialog(ExportStatus.USB_NOT_CONNECTED.value)
    dialog.continue_button.clicked.connect.assert_called_once_with(dialog._show_insert_usb_message)

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=True)
    dialog._update_dialog(ExportStatus.USB_NOT_CONNECTED.value)
    dialog._show_insert_usb_message.assert_called_once_with()


def test_ExportDialog__update_dialog_when_status_is_BAD_PASSPHRASE(mocker):
    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock_filename')
    dialog._show_passphrase_request_message_again = mocker.MagicMock()
    dialog.continue_button = mocker.MagicMock()
    dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    dialog._update_dialog(ExportStatus.BAD_PASSPHRASE.value)
    dialog.continue_button.clicked.connect.assert_called_once_with(
        dialog._show_passphrase_request_message_again)

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=True)
    dialog._update_dialog(ExportStatus.BAD_PASSPHRASE.value)
    dialog._show_passphrase_request_message_again.assert_called_once_with()


def test_ExportDialog__update_dialog_when_status_DISK_ENCRYPTION_NOT_SUPPORTED_ERROR(mocker):
    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock_filename')
    dialog._show_insert_encrypted_usb_message = mocker.MagicMock()
    dialog.continue_button = mocker.MagicMock()
    dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    dialog._update_dialog(ExportStatus.DISK_ENCRYPTION_NOT_SUPPORTED_ERROR.value)
    dialog.continue_button.clicked.connect.assert_called_once_with(
        dialog._show_insert_encrypted_usb_message)

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=True)
    dialog._update_dialog(ExportStatus.DISK_ENCRYPTION_NOT_SUPPORTED_ERROR.value)
    dialog._show_insert_encrypted_usb_message.assert_called_once_with()


def test_ExportDialog__update_dialog_when_status_is_CALLED_PROCESS_ERROR(mocker):
    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock_filename')
    dialog._show_generic_error_message = mocker.MagicMock()
    dialog.continue_button = mocker.MagicMock()
    dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    dialog._update_dialog(ExportStatus.CALLED_PROCESS_ERROR.value)
    dialog.continue_button.clicked.connect.assert_called_once_with(
        dialog._show_generic_error_message)
    assert dialog.error_status == ExportStatus.CALLED_PROCESS_ERROR.value

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=True)
    dialog._update_dialog(ExportStatus.CALLED_PROCESS_ERROR.value)
    dialog._show_generic_error_message.assert_called_once_with()
    assert dialog.error_status == ExportStatus.CALLED_PROCESS_ERROR.value


def test_ExportDialog__update_dialog_when_status_is_unknown(mocker):
    dialog = ExportDialog(mocker.MagicMock(), 'mock_uuid', 'mock_filename')
    dialog._show_generic_error_message = mocker.MagicMock()
    dialog.continue_button = mocker.MagicMock()
    dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    dialog._update_dialog('Some Unknown Error Status')
    dialog.continue_button.clicked.connect.assert_called_once_with(
        dialog._show_generic_error_message)
    assert dialog.error_status == 'Some Unknown Error Status'

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=True)
    dialog._update_dialog('Some Unknown Error Status')
    dialog._show_generic_error_message.assert_called_once_with()
    assert dialog.error_status == 'Some Unknown Error Status'


def test_PrintDialog_init(mocker):
    _show_starting_instructions_fn = mocker.patch(
        'securedrop_client.gui.widgets.PrintDialog._show_starting_instructions')

    PrintDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')

    _show_starting_instructions_fn.assert_called_once_with()


def test_PrintDialog_init_sanitizes_filename(mocker):
    secure_qlabel = mocker.patch('securedrop_client.gui.widgets.SecureQLabel')
    filename = '<script>alert("boom!");</script>'

    PrintDialog(mocker.MagicMock(), 'mock_uuid', filename)

    secure_qlabel.call_args_list[0].assert_called_with(filename)


def test_PrintDialog__show_starting_instructions(mocker):
    dialog = PrintDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')

    dialog._show_starting_instructions()

    assert dialog.header.text() == \
        'Preparing to print:' \
        '<br />' \
        '<span style="font-weight:normal">mock.jpg</span>'
    assert dialog.body.text() == \
        '<h2>Managing printout risks</h2>' \
        '<b>QR codes and web addresses</b>' \
        '<br />' \
        'Never type in and open web addresses or scan QR codes contained in printed ' \
        'documents without taking security precautions. If you are unsure how to ' \
        'manage this risk, please contact your administrator.' \
        '<br /><br />' \
        '<b>Printer dots</b>' \
        '<br />' \
        'Any part of a printed page may contain identifying information ' \
        'invisible to the naked eye, such as printer dots. Please carefully ' \
        'consider this risk when working with or publishing scanned printouts.'
    assert not dialog.header.isHidden()
    assert not dialog.header_line.isHidden()
    assert dialog.error_details.isHidden()
    assert not dialog.body.isHidden()
    assert not dialog.continue_button.isHidden()
    assert not dialog.cancel_button.isHidden()


def test_PrintDialog__show_insert_usb_message(mocker):
    dialog = PrintDialog(mocker.MagicMock(), 'mock_uuid', 'mock_filename')

    dialog._show_insert_usb_message()

    assert dialog.header.text() == 'Connect USB printer'
    assert dialog.body.text() == 'Please connect your printer to a USB port.'
    assert not dialog.header.isHidden()
    assert not dialog.header_line.isHidden()
    assert dialog.error_details.isHidden()
    assert not dialog.body.isHidden()
    assert not dialog.continue_button.isHidden()
    assert not dialog.cancel_button.isHidden()


def test_PrintDialog__show_generic_error_message(mocker):
    dialog = PrintDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')
    dialog.error_status = 'mock_error_status'

    dialog._show_generic_error_message()

    assert dialog.header.text() == 'Printing failed'
    assert dialog.body.text() == 'mock_error_status: See your administrator for help.'
    assert not dialog.header.isHidden()
    assert not dialog.header_line.isHidden()
    assert dialog.error_details.isHidden()
    assert not dialog.body.isHidden()
    assert not dialog.continue_button.isHidden()
    assert not dialog.cancel_button.isHidden()


def test_PrintDialog__print_file(mocker):
    dialog = PrintDialog(mocker.MagicMock(), 'mock_uuid', 'mock_filename')
    dialog.close = mocker.MagicMock()

    dialog._print_file()

    dialog.close.assert_called_once_with()


def test_PrintDialog__on_preflight_success(mocker):
    dialog = PrintDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')
    dialog._print_file = mocker.MagicMock()
    dialog.continue_button = mocker.MagicMock()
    dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=False)

    dialog._on_preflight_success()

    dialog._print_file.assert_not_called()
    dialog.continue_button.clicked.connect.assert_called_once_with(dialog._print_file)


def test_PrintDialog__on_preflight_success_when_continue_enabled(mocker):
    dialog = PrintDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')
    dialog._print_file = mocker.MagicMock()
    dialog.continue_button.setEnabled(True)

    dialog._on_preflight_success()

    dialog._print_file.assert_called_once_with()


def test_PrintDialog__on_preflight_success_enabled_after_preflight_success(mocker):
    dialog = PrintDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')
    assert not dialog.continue_button.isEnabled()
    dialog._on_preflight_success()
    assert dialog.continue_button.isEnabled()


def test_PrintDialog__on_preflight_success_enabled_after_preflight_failure(mocker):
    dialog = PrintDialog(mocker.MagicMock(), 'mock_uuid', 'mock.jpg')
    assert not dialog.continue_button.isEnabled()
    dialog._on_preflight_failure(mocker.MagicMock())
    assert dialog.continue_button.isEnabled()


def test_PrintDialog__on_preflight_failure_when_status_is_PRINTER_NOT_FOUND(mocker):
    dialog = PrintDialog(mocker.MagicMock(), 'mock_uuid', 'mock_filename')
    dialog._show_insert_usb_message = mocker.MagicMock()
    dialog.continue_button = mocker.MagicMock()
    dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    dialog._on_preflight_failure(ExportError(ExportStatus.PRINTER_NOT_FOUND.value))
    dialog.continue_button.clicked.connect.assert_called_once_with(dialog._show_insert_usb_message)

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=True)
    dialog._on_preflight_failure(ExportError(ExportStatus.PRINTER_NOT_FOUND.value))
    dialog._show_insert_usb_message.assert_called_once_with()


def test_PrintDialog__on_preflight_failure_when_status_is_MISSING_PRINTER_URI(mocker):
    dialog = PrintDialog(mocker.MagicMock(), 'mock_uuid', 'mock_filename')
    dialog._show_generic_error_message = mocker.MagicMock()
    dialog.continue_button = mocker.MagicMock()
    dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    dialog._on_preflight_failure(ExportError(ExportStatus.MISSING_PRINTER_URI.value))
    dialog.continue_button.clicked.connect.assert_called_once_with(
        dialog._show_generic_error_message)
    assert dialog.error_status == ExportStatus.MISSING_PRINTER_URI.value

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=True)
    dialog._on_preflight_failure(ExportError(ExportStatus.MISSING_PRINTER_URI.value))
    dialog._show_generic_error_message.assert_called_once_with()
    assert dialog.error_status == ExportStatus.MISSING_PRINTER_URI.value


def test_PrintDialog__on_preflight_failure_when_status_is_CALLED_PROCESS_ERROR(mocker):
    dialog = PrintDialog(mocker.MagicMock(), 'mock_uuid', 'mock_filename')
    dialog._show_generic_error_message = mocker.MagicMock()
    dialog.continue_button = mocker.MagicMock()
    dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    dialog._on_preflight_failure(ExportError(ExportStatus.CALLED_PROCESS_ERROR.value))
    dialog.continue_button.clicked.connect.assert_called_once_with(
        dialog._show_generic_error_message)
    assert dialog.error_status == ExportStatus.CALLED_PROCESS_ERROR.value

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=True)
    dialog._on_preflight_failure(ExportError(ExportStatus.CALLED_PROCESS_ERROR.value))
    dialog._show_generic_error_message.assert_called_once_with()
    assert dialog.error_status == ExportStatus.CALLED_PROCESS_ERROR.value


def test_PrintDialog__on_preflight_failure_when_status_is_unknown(mocker):
    dialog = PrintDialog(mocker.MagicMock(), 'mock_uuid', 'mock_filename')
    dialog._show_generic_error_message = mocker.MagicMock()
    dialog.continue_button = mocker.MagicMock()
    dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    dialog._on_preflight_failure(ExportError('Some Unknown Error Status'))
    dialog.continue_button.clicked.connect.assert_called_once_with(
        dialog._show_generic_error_message)
    assert dialog.error_status == 'Some Unknown Error Status'

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(dialog.continue_button, 'isEnabled', return_value=True)
    dialog._on_preflight_failure(ExportError('Some Unknown Error Status'))
    dialog._show_generic_error_message.assert_called_once_with()
    assert dialog.error_status == 'Some Unknown Error Status'


def test_SourceConversationWrapper__on_source_deleted(mocker):
    scw = SourceConversationWrapper(factory.Source(uuid='123'), mocker.MagicMock())
    scw._on_source_deleted('123')
    assert scw.conversation_title_bar.isHidden()
    assert scw.conversation_view.isHidden()
    assert scw.reply_box.isHidden()
    assert not scw.waiting_delete_confirmation.isHidden()


def test_SourceConversationWrapper__on_source_deleted_wrong_uuid(mocker):
    scw = SourceConversationWrapper(factory.Source(uuid='123'), mocker.MagicMock())
    scw._on_source_deleted('321')
    assert not scw.conversation_title_bar.isHidden()
    assert not scw.conversation_view.isHidden()
    assert not scw.reply_box.isHidden()
    assert scw.waiting_delete_confirmation.isHidden()


def test_SourceConversationWrapper__on_source_deletion_failed(mocker):
    scw = SourceConversationWrapper(factory.Source(uuid='123'), mocker.MagicMock())
    scw._on_source_deleted('123')

    scw._on_source_deletion_failed('123')

    assert not scw.conversation_title_bar.isHidden()
    assert not scw.conversation_view.isHidden()
    assert not scw.reply_box.isHidden()
    assert scw.waiting_delete_confirmation.isHidden()


def test_SourceConversationWrapper__on_source_deletion_failed_wrong_uuid(mocker):
    scw = SourceConversationWrapper(factory.Source(uuid='123'), mocker.MagicMock())
    scw._on_source_deleted('123')

    scw._on_source_deletion_failed('321')

    assert scw.conversation_title_bar.isHidden()
    assert scw.conversation_view.isHidden()
    assert scw.reply_box.isHidden()
    assert not scw.waiting_delete_confirmation.isHidden()


def test_ConversationView_init(mocker, homedir):
    """
    Ensure the conversation view has a layout to add widgets to.
    """
    mocked_source = mocker.MagicMock()
    mocked_controller = mocker.MagicMock()
    cv = ConversationView(mocked_source, mocked_controller)
    assert isinstance(cv.conversation_layout, QVBoxLayout)


def test_ConversationView_update_conversation_position_follow(mocker, homedir):
    """
    Check the signal handler sets the correct value for the scrollbar to be
    the maximum possible value, when the scrollbar is near the bottom, meaning
    it is following the conversation. This should only work if the user has
    submitted a reply to a source.
    """
    mocked_source = mocker.MagicMock()
    mocked_controller = mocker.MagicMock()

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
    mocked_controller = mocker.MagicMock()

    cv = ConversationView(mocked_source, mocked_controller)

    cv.scroll.verticalScrollBar().value = mocker.MagicMock(return_value=5500)
    cv.scroll.viewport().height = mocker.MagicMock(return_value=500)
    cv.scroll.verticalScrollBar().setValue = mocker.MagicMock()

    cv.update_conversation_position(0, 6000)

    cv.scroll.verticalScrollBar().setValue.assert_not_called()


def test_ConversationView_add_message(mocker, session, source):
    """
    Adding a message results in a new MessageWidget added to the layout.
    """
    source = source['source']  # grab the source from the fixture dict for simplicity

    mock_message_ready_signal = mocker.MagicMock()
    mock_message_download_failed_signal = mocker.MagicMock()
    mocked_controller = mocker.MagicMock(
        session=session,
        message_ready=mock_message_ready_signal,
        message_download_failed=mock_message_download_failed_signal,
    )

    content = 'a sea, a bee'
    message = factory.Message(source=source, content=content)
    session.add(message)
    session.commit()

    cv = ConversationView(source, mocked_controller)
    cv.conversation_layout = mocker.MagicMock()
    cv.conversation_updated = mocker.MagicMock()
    # this is the MessageWidget that __init__() would return
    mock_msg_widget_res = mocker.MagicMock()
    # mock the actual MessageWidget so we can inspect the __init__ call
    mock_msg_widget = mocker.patch('securedrop_client.gui.widgets.MessageWidget',
                                   return_value=mock_msg_widget_res)

    cv.add_message(message, 0)

    # check that we built the widget was called with the correct args
    mock_msg_widget.assert_called_once_with(
        message.uuid,
        content,
        mock_message_ready_signal,
        mock_message_download_failed_signal,
        0,
        False,
    )

    # check that we added the correct widget to the layout
    cv.conversation_layout.insertWidget.assert_called_once_with(
        0, mock_msg_widget_res, alignment=Qt.AlignLeft)

    # Check the signal is emitted to say the message has been added (and thus
    # the timestamps need updating.
    assert cv.conversation_updated.emit.call_count == 1


def test_ConversationView_add_message_no_content(mocker, session, source):
    """
    Adding a message results in a new MessageWidget added to the layout. This case specifically
    checks that if a `Message` has `content = None` that a helpful message is displayed as would
    be the case if download/decryption never occurred or failed.
    """
    source = source['source']  # grab the source from the fixture dict for simplicity

    mock_message_ready_signal = mocker.MagicMock()
    mock_message_download_failed_signal = mocker.MagicMock()
    mocked_controller = mocker.MagicMock(
        session=session,
        message_ready=mock_message_ready_signal,
        message_download_failed=mock_message_download_failed_signal
    )

    message = factory.Message(source=source, is_decrypted=False, content=None)
    session.add(message)
    session.commit()

    cv = ConversationView(source, mocked_controller)
    cv.conversation_layout = mocker.MagicMock()
    # this is the MessageWidget that __init__() would return
    mock_msg_widget_res = mocker.MagicMock()
    # mock the actual MessageWidget so we can inspect the __init__ call
    mock_msg_widget = mocker.patch('securedrop_client.gui.widgets.MessageWidget',
                                   return_value=mock_msg_widget_res)

    cv.add_message(message, 0)

    # check that we built the widget was called with the correct args
    mock_msg_widget.assert_called_once_with(
        message.uuid, '<Message not yet available>', mock_message_ready_signal,
        mock_message_download_failed_signal, 0, False
    )

    # check that we added the correct widget to the layout
    cv.conversation_layout.insertWidget.assert_called_once_with(
        0, mock_msg_widget_res, alignment=Qt.AlignLeft)


def test_ConversationView_on_reply_sent(mocker):
    """
    The handler for new replies should call add_reply
    """
    source = factory.Source()
    controller = mocker.MagicMock()
    cv = ConversationView(source, controller)
    cv.add_reply_from_reply_box = mocker.MagicMock()

    assert cv.reply_flag is False
    cv.on_reply_sent(source.uuid, 'abc123', 'test message')

    cv.add_reply_from_reply_box.assert_called_with('abc123', 'test message')
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

    cv.on_reply_sent('different_source_id', 'mock', 'mock')

    assert not cv.add_reply.called


def test_ConversationView_add_reply_from_reply_box(mocker):
    """
    Adding a reply from reply box results in a new ReplyWidget added to the layout.
    """
    source = factory.Source()
    reply_ready = mocker.MagicMock()
    reply_download_failed = mocker.MagicMock()
    reply_succeeded = mocker.MagicMock()
    reply_failed = mocker.MagicMock()
    controller = mocker.MagicMock(
        reply_ready=reply_ready,
        reply_download_failed=reply_download_failed,
        reply_succeeded=reply_succeeded,
        reply_failed=reply_failed
    )
    cv = ConversationView(source, controller)
    cv.conversation_layout = mocker.MagicMock()
    reply_widget_res = mocker.MagicMock()
    reply_widget = mocker.patch(
        'securedrop_client.gui.widgets.ReplyWidget', return_value=reply_widget_res)

    cv.add_reply_from_reply_box('abc123', 'test message')

    reply_widget.assert_called_once_with(
        'abc123', 'test message', 'PENDING', reply_ready, reply_download_failed,
        reply_succeeded, reply_failed, 0
    )
    cv.conversation_layout.insertWidget.assert_called_once_with(
        0, reply_widget_res, alignment=Qt.AlignRight)


def test_ConversationView_add_reply(mocker, session, source):
    """
    Adding a reply from a source results in a new ReplyWidget added to the layout.
    """
    source = source['source']  # grab the source from the fixture dict for simplicity

    mock_reply_ready_signal = mocker.MagicMock()
    mock_reply_download_failed_signal = mocker.MagicMock()
    mock_reply_succeeded_signal = mocker.MagicMock()
    mock_reply_failed_signal = mocker.MagicMock()
    mocked_controller = mocker.MagicMock(
        session=session,
        reply_ready=mock_reply_ready_signal,
        reply_download_failed=mock_reply_download_failed_signal,
        reply_succeeded=mock_reply_succeeded_signal,
        reply_failed=mock_reply_failed_signal
    )

    content = 'a sea, a bee'
    reply = factory.Reply(source=source, content=content)
    session.add(reply)
    session.commit()

    cv = ConversationView(source, mocked_controller)
    cv.conversation_layout = mocker.MagicMock()
    # this is the Reply that __init__() would return
    reply_widget_res = mocker.MagicMock()
    # mock the actual MessageWidget so we can inspect the __init__ call
    mock_reply_widget = mocker.patch('securedrop_client.gui.widgets.ReplyWidget',
                                     return_value=reply_widget_res)

    cv.add_reply(reply, 0)

    # check that we built the widget was called with the correct args
    mock_reply_widget.assert_called_once_with(
        reply.uuid,
        content,
        'SUCCEEDED',
        mock_reply_ready_signal,
        mock_reply_download_failed_signal,
        mock_reply_succeeded_signal,
        mock_reply_failed_signal,
        0,
        False
    )

    # check that we added the correct widget to the layout
    cv.conversation_layout.insertWidget.assert_called_once_with(
        0, reply_widget_res, alignment=Qt.AlignRight)


def test_ConversationView_add_reply_no_content(mocker, session, source):
    """
    Adding a reply results in a new ReplyWidget added to the layout. This case specifically
    checks that if a `Reply` has `content = None` that a helpful message is displayed as would
    be the case if download/decryption never occurred or failed.
    """
    source = source['source']  # grab the source from the fixture dict for simplicity

    mock_reply_ready_signal = mocker.MagicMock()
    mock_reply_download_failed_signal = mocker.MagicMock()
    mock_reply_succeeded_signal = mocker.MagicMock()
    mock_reply_failed_signal = mocker.MagicMock()
    mocked_controller = mocker.MagicMock(session=session,
                                         reply_ready=mock_reply_ready_signal,
                                         reply_download_failed=mock_reply_download_failed_signal,
                                         reply_succeeded=mock_reply_succeeded_signal,
                                         reply_failed=mock_reply_failed_signal)

    reply = factory.Reply(source=source, is_decrypted=False, content=None)
    session.add(reply)
    session.commit()

    cv = ConversationView(source, mocked_controller)
    cv.conversation_layout = mocker.MagicMock()
    # this is the Reply that __init__() would return
    reply_widget_res = mocker.MagicMock()
    # mock the actual MessageWidget so we can inspect the __init__ call
    mock_reply_widget = mocker.patch('securedrop_client.gui.widgets.ReplyWidget',
                                     return_value=reply_widget_res)

    cv.add_reply(reply, 0)

    # check that we built the widget was called with the correct args
    mock_reply_widget.assert_called_once_with(
        reply.uuid,
        '<Reply not yet available>',
        'SUCCEEDED',
        mock_reply_ready_signal,
        mock_reply_download_failed_signal,
        mock_reply_succeeded_signal,
        mock_reply_failed_signal,
        0,
        False
    )

    # check that we added the correct widget to the layout
    cv.conversation_layout.insertWidget.assert_called_once_with(
        0, reply_widget_res, alignment=Qt.AlignRight)


def test_ConversationView_add_downloaded_file(mocker, homedir, source, session):
    """
    Adding a file results in a new FileWidget added to the layout with the
    proper QLabel.
    """
    file = factory.File(source=source['source'])
    file.is_downloaded = True
    session.add(file)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file)
    mocked_controller = mocker.MagicMock(get_file=mock_get_file)

    cv = ConversationView(source['source'], mocked_controller)
    cv.conversation_layout = mocker.MagicMock()
    cv.conversation_updated = mocker.MagicMock()

    mock_label = mocker.patch('securedrop_client.gui.widgets.SecureQLabel')
    mocker.patch('securedrop_client.gui.widgets.QHBoxLayout.addWidget')
    mocker.patch('securedrop_client.gui.widgets.FileWidget.setLayout')

    cv.add_file(file, 0)

    mock_label.assert_called_with('123B')  # default factory filesize
    assert cv.conversation_layout.insertWidget.call_count == 1
    assert cv.conversation_updated.emit.call_count == 1

    cal = cv.conversation_layout.insertWidget.call_args_list
    assert isinstance(cal[0][0][1], FileWidget)


def test_ConversationView_add_not_downloaded_file(mocker, homedir, source, session):
    """
    Adding a file results in a new FileWidget added to the layout with the
    proper QLabel.
    """
    file = factory.File(source=source['source'], is_downloaded=False, is_decrypted=None, size=123)
    session.add(file)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file)
    mocked_controller = mocker.MagicMock(get_file=mock_get_file)

    cv = ConversationView(source['source'], mocked_controller)
    cv.conversation_layout = mocker.MagicMock()

    mocker.patch('securedrop_client.gui.widgets.QHBoxLayout.addWidget')
    mocker.patch('securedrop_client.gui.widgets.FileWidget.setLayout')

    cv.add_file(file, 0)
    assert cv.conversation_layout.insertWidget.call_count == 1

    cal = cv.conversation_layout.insertWidget.call_args_list
    assert isinstance(cal[0][0][1], FileWidget)


def test_DeleteSourceMessageBox_init(mocker, source):
    mock_controller = mocker.MagicMock()
    DeleteSourceMessageBox(source['source'], mock_controller)


def test_DeleteSourceMessage_launch_when_user_chooses_cancel(mocker, source):
    source = source['source']  # to get the Source object

    mock_message_box_question = mocker.MagicMock(QMessageBox.question)
    mock_message_box_question.return_value = QMessageBox.Cancel
    mock_controller = mocker.MagicMock()

    delete_source_message_box = DeleteSourceMessageBox(source, mock_controller)

    mocker.patch(
        "securedrop_client.gui.widgets.QMessageBox.question",
        mock_message_box_question,
    )

    delete_source_message_box.launch()
    mock_controller.delete_source.assert_not_called()


def test_DeleteSourceMssageBox_launch_when_user_chooses_yes(mocker, source, session):
    source = source['source']  # to get the Source object
    file_ = factory.File(source=source)
    session.add(file_)
    message = factory.Message(source=source)
    session.add(message)
    message = factory.Message(source=source)
    session.add(message)
    reply = factory.Reply(source=source)
    session.add(reply)
    session.commit()

    mock_message_box_question = mocker.MagicMock(QMessageBox.question)
    mock_message_box_question.return_value = QMessageBox.Yes
    mock_controller = mocker.MagicMock()

    delete_source_message_box = DeleteSourceMessageBox(source, mock_controller)

    mocker.patch(
        "securedrop_client.gui.widgets.QMessageBox.question",
        mock_message_box_question,
    )

    delete_source_message_box.launch()
    mock_controller.delete_source.assert_called_once_with(source)

    message = (
        "<big>Deleting the Source account for "
        "<b>{designation}</b> will also "
        "delete {files} files, {replies} replies, and {messages} messages.</big>"
        " <br> "
        "<small>This Source will no longer be able to correspond "
        "through the log-in tied to this account.</small>"
    ).format(designation=source.journalist_designation, files=1, replies=1, messages=2)
    mock_message_box_question.assert_called_once_with(
        None,
        "",
        message,
        QMessageBox.Cancel | QMessageBox.Yes,
        QMessageBox.Cancel
    )


def test_DeleteSourceMessageBox_construct_message(mocker, source, session):
    source = source['source']  # to get the Source object
    file_ = factory.File(source=source)
    session.add(file_)
    message = factory.Message(source=source)
    session.add(message)
    message = factory.Message(source=source)
    session.add(message)
    reply = factory.Reply(source=source)
    session.add(reply)
    session.commit()

    mock_controller = mocker.MagicMock()

    delete_source_message_box = DeleteSourceMessageBox(source, mock_controller)

    message = delete_source_message_box._construct_message(source)

    expected_message = (
        "<big>Deleting the Source account for "
        "<b>{designation}</b> will also "
        "delete {files} files, {replies} replies, and {messages} messages.</big>"
        " <br> "
        "<small>This Source will no longer be able to correspond "
        "through the log-in tied to this account.</small>"
    ).format(designation=source.journalist_designation, files=1, replies=1, messages=2)
    assert message == expected_message


def test_DeleteSourceAction_init(mocker):
    mock_controller = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    DeleteSourceAction(
        mock_source,
        None,
        mock_controller
    )


def test_PasswordEdit(mocker):
    passwordline = PasswordEdit(None)
    passwordline.togglepasswordAction.trigger()

    assert passwordline.echoMode() == QLineEdit.Normal
    passwordline.togglepasswordAction.trigger()
    assert passwordline.echoMode() == QLineEdit.Password


def test_DeleteSourceAction_trigger(mocker):
    mock_controller = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    mock_delete_source_message_box_obj = mocker.MagicMock()
    mock_delete_source_message_box = mocker.MagicMock()
    mock_delete_source_message_box.return_value = (
        mock_delete_source_message_box_obj
    )

    with mocker.patch(
        'securedrop_client.gui.widgets.DeleteSourceMessageBox',
        mock_delete_source_message_box
    ):
        delete_source_action = DeleteSourceAction(
            mock_source,
            None,
            mock_controller
        )
        delete_source_action.trigger()
        mock_delete_source_message_box_obj.launch.assert_called_once_with()


def test_DeleteSource_from_source_menu_when_user_is_loggedout(mocker):
    mock_source = mocker.MagicMock()
    mock_controller = mocker.MagicMock(logic.Controller)
    mock_controller.api = None
    mock_delete_source_message_box_obj = mocker.MagicMock()
    mock_delete_source_message_box = mocker.MagicMock()
    mock_delete_source_message_box.return_value = (
        mock_delete_source_message_box_obj
    )

    with mocker.patch(
        'securedrop_client.gui.widgets.DeleteSourceMessageBox',
        mock_delete_source_message_box
    ):
        source_menu = SourceMenu(mock_source, mock_controller)
        source_menu.actions()[0].trigger()
        mock_delete_source_message_box_obj.launch.assert_not_called()


def test_DeleteSource_from_source_widget_when_user_is_loggedout(mocker):
    mock_source = mocker.MagicMock(journalist_designation='mock')
    mock_controller = mocker.MagicMock()
    mock_controller.api = None
    mock_event = mocker.MagicMock()
    mock_delete_source_message_box_obj = mocker.MagicMock()
    mock_delete_source_message_box = mocker.MagicMock()
    mock_delete_source_message_box.return_value = (
        mock_delete_source_message_box_obj
    )

    with mocker.patch(
        'securedrop_client.gui.widgets.DeleteSourceMessageBox',
        mock_delete_source_message_box
    ):
        source_widget = SourceWidget(mock_controller, mock_source)
        source_widget.delete_source(mock_event)
        mock_delete_source_message_box_obj.launch.assert_not_called()


def test_ReplyBoxWidget_init(mocker):
    """
    Ensure reply box set up properly.
    """
    rb = ReplyBoxWidget(mocker.MagicMock(), mocker.MagicMock())
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
    rb = ReplyBoxWidget(mocker.MagicMock(), controller)
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
    assert rb.text_edit.placeholder.text().find(source.journalist_designation) != -1


def test_ReplyBoxWidget_send_reply(mocker):
    """
    Ensure sending a reply from the reply box emits signal, clears text box, and sends the reply
    details to the controller.
    """
    source = mocker.Mock()
    source.uuid = 'abc123'
    source.collection = []
    reply_uuid = '456xyz'
    mocker.patch('securedrop_client.gui.widgets.uuid4', return_value=reply_uuid)
    controller = mocker.MagicMock()
    mocker.patch('securedrop_client.gui.widgets.SourceProfileShortWidget')
    mocker.patch('securedrop_client.gui.widgets.QVBoxLayout.addWidget')
    scw = SourceConversationWrapper(source, controller)
    on_reply_sent_fn = mocker.MagicMock()
    scw.conversation_view.on_reply_sent = on_reply_sent_fn
    scw.reply_box.reply_sent = mocker.MagicMock()
    scw.reply_box.text_edit = ReplyTextEdit(source, controller)
    scw.reply_box.text_edit.setText = mocker.MagicMock()
    scw.reply_box.text_edit.setPlainText('Alles für Alle')

    scw.reply_box.send_reply()

    scw.reply_box.reply_sent.emit.assert_called_once_with('abc123', '456xyz', 'Alles für Alle')
    scw.reply_box.text_edit.setText.assert_called_once_with('')
    controller.send_reply.assert_called_once_with('abc123', '456xyz', 'Alles für Alle')


def test_ReplyBoxWidget_send_reply_calls_setText_after_send(mocker):
    """
    Ensure sending a reply from the reply box emits signal, clears text box, and sends the reply
    details to the controller.
    """
    source = factory.Source()
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.text_edit = ReplyTextEdit(source, controller)
    setText = mocker.patch.object(rb.text_edit, 'setText')
    rb.text_edit.setPlainText('Alles für Alle')

    rb.send_reply()

    setText.assert_called_once_with('')


def test_ReplyBoxWidget_send_reply_does_not_send_empty_string(mocker):
    """
    Ensure sending a reply from the reply box does not send empty string.
    """
    source = mocker.MagicMock()
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.text_edit = ReplyTextEdit(source, controller)
    assert not rb.text_edit.toPlainText()

    rb.send_reply()

    assert not controller.send_reply.called

    # Also check that we don't send blank space
    rb.text_edit.setText('  \n\n  ')

    rb.send_reply()

    assert not controller.send_reply.called


def test_ReplyBoxWidget_on_synced(mocker):
    source = mocker.MagicMock()
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.text_edit.hasFocus = mocker.MagicMock(return_value=True)
    rb.text_edit.setFocus = mocker.MagicMock()

    rb._on_synced("syncing")
    assert rb.refocus_after_sync is True

    rb._on_synced("synced")
    rb.text_edit.setFocus.assert_called_once_with()

    rb.text_edit.hasFocus.return_value = False
    rb._on_synced("syncing")
    assert rb.refocus_after_sync is False


def test_ReplyBoxWidget_on_sync_source_deleted(mocker, source):
    s = source['source']
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(s, controller)

    error_logger = mocker.patch('securedrop_client.gui.widgets.logger.debug')

    def pretend_source_was_deleted(self):
        raise sqlalchemy.orm.exc.ObjectDeletedError(
            attributes.instance_state(s), None
        )

    with patch.object(ReplyBoxWidget, 'update_authentication_state') as uas:
        uas.side_effect = pretend_source_was_deleted
        rb._on_synced("syncing")
        error_logger.assert_called_once_with(
            "During sync, ReplyBoxWidget found its source had been deleted."
        )


def test_ReplyWidget_success_failure_slots(mocker):
    mock_update_signal = mocker.Mock()
    mock_download_failed_signal = mocker.Mock()
    mock_success_signal = mocker.Mock()
    mock_failure_signal = mocker.Mock()
    msg_id = 'abc123'

    widget = ReplyWidget(msg_id,
                         'lol',
                         'PENDING',
                         mock_update_signal,
                         mock_download_failed_signal,
                         mock_success_signal,
                         mock_failure_signal,
                         0)

    # ensure we have connected the slots
    mock_success_signal.connect.assert_called_once_with(widget._on_reply_success)
    mock_failure_signal.connect.assert_called_once_with(widget._on_reply_failure)
    assert mock_update_signal.connect.called  # to ensure no stale mocks
    assert mock_download_failed_signal.connect.called

    # check the success slog
    widget._on_reply_success('mock_source_id', msg_id + "x", 'lol')
    assert widget.error.isHidden()
    widget._on_reply_success('mock_source_id', msg_id, 'lol')
    assert widget.error.isHidden()

    # check the failure slot where message id does not match
    widget._on_reply_failure(msg_id + "x")
    assert widget.error.isHidden()
    # check the failure slot where message id matches
    widget._on_reply_failure(msg_id)
    assert not widget.error.isHidden()


def test_ReplyBoxWidget__on_authentication_changed(mocker, homedir):
    """
    When the client is authenticated, enable reply box.
    """
    source = mocker.MagicMock()
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.set_logged_in = mocker.MagicMock()

    rb._on_authentication_changed(True)

    rb.set_logged_in.assert_called_once_with()


def test_ReplyBoxWidget_on_authentication_changed_source_deleted(mocker, source):
    s = source['source']
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(s, controller)

    error_logger = mocker.patch('securedrop_client.gui.widgets.logger.debug')

    def pretend_source_was_deleted(self):
        raise sqlalchemy.orm.exc.ObjectDeletedError(
            attributes.instance_state(s), None
        )

    with patch.object(ReplyBoxWidget, 'update_authentication_state') as uas:
        uas.side_effect = pretend_source_was_deleted
        rb._on_authentication_changed(True)
        error_logger.assert_called_once_with(
            "On authentication change, ReplyBoxWidget found its source had been deleted."
        )


def test_ReplyBoxWidget__on_authentication_changed_offline(mocker, homedir):
    """
    When the client goes offline, disable reply box.
    """
    source = mocker.MagicMock()
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.set_logged_out = mocker.MagicMock()

    rb._on_authentication_changed(False)

    rb.set_logged_out.assert_called_once_with()


def test_ReplyBoxWidget_auth_signals(mocker, homedir):
    """
    Ensure we connect to the auth signal and set the intial state on update
    """
    source = mocker.Mock(collection=[])
    connect = mocker.MagicMock()
    signal = mocker.MagicMock(connect=connect)
    controller = mocker.MagicMock(authentication_state=signal)
    controller.is_authenticated = False

    _on_authentication_changed_fn = mocker.patch.object(
        ReplyBoxWidget, '_on_authentication_changed')

    ReplyBoxWidget(source, controller)

    connect.assert_called_once_with(_on_authentication_changed_fn)


def test_ReplyBoxWidget_enable(mocker):
    source = mocker.MagicMock()
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.text_edit = ReplyTextEdit(source, controller)
    rb.text_edit.set_logged_in = mocker.MagicMock()
    rb.send_button = mocker.MagicMock()

    rb.set_logged_in()

    assert rb.text_edit.toPlainText() == ''
    rb.text_edit.set_logged_in.assert_called_once_with()
    rb.send_button.show.assert_called_once_with()


def test_ReplyBoxWidget_disable(mocker):
    source = mocker.MagicMock()
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.text_edit = ReplyTextEdit(source, controller)
    rb.text_edit.set_logged_out = mocker.MagicMock()
    rb.send_button = mocker.MagicMock()

    rb.set_logged_out()

    assert rb.text_edit.toPlainText() == ''
    rb.text_edit.set_logged_out.assert_called_once_with()
    rb.send_button.hide.assert_called_once_with()


def test_ReplyBoxWidget_enable_after_source_gets_key(mocker, session, session_maker, homedir):
    """
    Test that it's enabled when a source that lacked a key now has one.
    """

    with mocker.patch('sdclientapi.API'):
        mock_gui = mocker.MagicMock()
        controller = logic.Controller('http://localhost', mock_gui, session_maker, homedir)
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
        storage.update_sources([source_with_key], [source], session, homedir)

        # ... simulate the ReplyBoxWidget receiving the sync success signal
        rbw._on_synced("synced")

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
    source = mocker.MagicMock()
    controller = mocker.MagicMock()
    rt = ReplyTextEdit(source, controller)

    focus_in_event = QFocusEvent(QEvent.FocusIn)
    focus_out_event = QFocusEvent(QEvent.FocusOut)

    rt.focusInEvent(focus_in_event)
    assert rt.placeholder.isHidden()
    assert rt.toPlainText() == ''

    rt.focusOutEvent(focus_out_event)
    assert not rt.placeholder.isHidden()
    assert rt.toPlainText() == ''


def test_ReplyTextEdit_focus_change_with_text_typed(mocker):
    """
    Test that the placeholder does not appear when there is text in the ReplyTextEdit widget and
    that the text remains in the ReplyTextEdit regardless of focus.
    """
    source = mocker.MagicMock()
    controller = mocker.MagicMock()
    rt = ReplyTextEdit(source, controller)
    reply_text = 'mocked reply text'
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
    rt = ReplyTextEdit(mocker.MagicMock(), mocker.MagicMock())
    mocker.patch('securedrop_client.gui.widgets.QPlainTextEdit.setPlainText')

    rt.setText('mocked reply text')

    assert rt.placeholder.isHidden()
    rt.setPlainText.assert_called_once_with('mocked reply text')


def test_ReplyTextEdit_setText_empty_string(mocker):
    """
    Checks that plain string parameter causes placeholder to show and that super's setPlainText
    method is called (to ensure cursor is hidden).
    """
    rt = ReplyTextEdit(mocker.MagicMock(), mocker.MagicMock())
    mocker.patch('securedrop_client.gui.widgets.QPlainTextEdit.setPlainText')

    rt.setText('')

    assert not rt.placeholder.isHidden()
    rt.setPlainText.assert_called_once_with('')


def test_ReplyTextEdit_set_logged_out(mocker):
    """
    Checks the placeholder text for reply box is correct for offline mode
    """
    source = mocker.MagicMock()
    controller = mocker.MagicMock()
    rt = ReplyTextEdit(source, controller)

    rt.set_logged_out()

    assert 'Sign in' in rt.placeholder.text()
    assert 'to compose or send a reply' in rt.placeholder.text()


def test_ReplyTextEdit_set_logged_in(mocker):
    """
    Checks the placeholder text for reply box is correct for online mode
    """
    source = mocker.MagicMock()
    source.journalist_designation = 'journalist designation'
    controller = mocker.MagicMock()
    rt = ReplyTextEdit(source, controller)

    rt.set_logged_in()

    assert 'Compose a reply to' in rt.placeholder.text()
    assert source.journalist_designation in rt.placeholder.text()


def test_ReplyBox_set_logged_in_no_public_key(mocker):
    """
    If the selected source has no public key, ensure a warning message is
    shown and the user is unable to send a reply.
    """
    source = mocker.MagicMock()
    source.journalist_designation = 'journalist designation'
    source.public_key = None
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)

    rb.set_logged_in()

    assert 'Awaiting encryption key' in rb.text_edit.placeholder.text()

    # Both the reply box and the text editor must be disabled for the widget
    # to be rendered correctly.
    assert rb.replybox.isEnabled() is False
    assert rb.text_edit.isEnabled() is False


def test_update_conversation_maintains_old_items(mocker, session):
    """
    Calling update_conversation maintains old item state / position if there's
    no change to the conversation collection.
    """
    source = factory.Source()
    session.add(source)
    session.commit()

    file_ = factory.File(filename='1-source-doc.gpg', source=source)
    session.add(file_)
    message = factory.Message(filename='2-source-msg.gpg', source=source)
    session.add(message)
    reply = factory.Reply(filename='3-source-reply.gpg', source=source)
    session.add(reply)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file_)
    mock_controller = mocker.MagicMock(get_file=mock_get_file)

    cv = ConversationView(source, mock_controller)
    assert cv.conversation_layout.count() == 3

    cv.update_conversation(cv.source.collection)

    assert cv.conversation_layout.count() == 3


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

    file_ = factory.File(filename='1-source-doc.gpg', source=source)
    session.add(file_)
    message = factory.Message(filename='2-source-msg.gpg', source=source)
    session.add(message)
    draft_reply = factory.DraftReply(source=source, send_status=send_status)
    session.add(draft_reply)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file_)
    mock_controller = mocker.MagicMock(get_file=mock_get_file)

    cv = ConversationView(source, mock_controller)
    assert cv.conversation_layout.count() == 3  # precondition with draft

    # add the new message and persist
    new_message = factory.Message(filename='4-source-msg.gpg', source=source)
    session.add(new_message)
    session.commit()

    # New message added, draft message persists.
    cv.update_conversation(cv.source.collection)
    assert cv.conversation_layout.count() == 4


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

    file_ = factory.File(filename='1-source-doc.gpg', source=source)
    session.add(file_)
    message = factory.Message(filename='2-source-msg.gpg', source=source)
    session.add(message)
    draft_reply = factory.DraftReply(source=source, send_status=send_status)
    session.add(draft_reply)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file_)
    mock_controller = mocker.MagicMock(get_file=mock_get_file)

    cv = ConversationView(source, mock_controller)
    assert cv.conversation_layout.count() == 3  # precondition with draft

    # add the new message and persist
    new_message = factory.Message(filename='4-source-msg.gpg', source=source)
    session.add(new_message)
    session.commit()

    # remove draft
    session.delete(draft_reply)
    session.commit()

    # New message added, draft message is gone.
    cv.update_conversation(cv.source.collection)
    assert cv.conversation_layout.count() == 3


def test_update_conversation_keeps_failed_draft_items(mocker, session):
    """
    Calling update_conversation keeps items that were added as drafts but which
    have failed.
    """
    source = factory.Source()
    session.add(source)
    send_status = factory.ReplySendStatus(name="FAILED")
    session.add(send_status)
    session.commit()

    file_ = factory.File(filename='1-source-doc.gpg', source=source)
    session.add(file_)
    message = factory.Message(filename='2-source-msg.gpg', source=source)
    session.add(message)
    draft_reply = factory.DraftReply(source=source, send_status=send_status)
    session.add(draft_reply)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file_)
    mock_controller = mocker.MagicMock(get_file=mock_get_file)

    cv = ConversationView(source, mock_controller)
    assert cv.conversation_layout.count() == 3  # precondition with draft

    # add the new message and persist
    new_message = factory.Message(filename='4-source-msg.gpg', source=source)
    session.add(new_message)
    session.commit()

    # New message added, draft message retained.
    cv.update_conversation(cv.source.collection)
    assert cv.conversation_layout.count() == 4


def test_update_conversation_adds_new_items(mocker, session):
    """
    Calling update_conversation adds new items to layout
    """
    source = factory.Source()
    session.add(source)
    session.commit()

    file_ = factory.File(filename='1-source-doc.gpg', source=source)
    session.add(file_)
    message = factory.Message(filename='2-source-msg.gpg', source=source)
    session.add(message)
    reply = factory.Reply(filename='3-source-reply.gpg', source=source)
    session.add(reply)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file_)
    mock_controller = mocker.MagicMock(get_file=mock_get_file)

    cv = ConversationView(source, mock_controller)
    assert cv.conversation_layout.count() == 3  # precondition

    # add the new message and persist
    new_message = factory.Message(filename='4-source-msg.gpg', source=source)
    session.add(new_message)
    session.commit()

    cv.update_conversation(cv.source.collection)
    assert cv.conversation_layout.count() == 4


def test_update_conversation_position_updates(mocker, session):
    """
    Calling update_conversation adds new items to layout
    """
    source = factory.Source()
    session.add(source)
    session.commit()

    file_ = factory.File(filename='1-source-doc.gpg', source=source)
    session.add(file_)
    message = factory.Message(filename='2-source-msg.gpg', source=source)
    session.add(message)
    reply = factory.Reply(filename='3-source-reply.gpg', source=source)
    session.add(reply)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file_)
    mock_controller = mocker.MagicMock(get_file=mock_get_file)

    cv = ConversationView(source, mock_controller)
    assert cv.conversation_layout.count() == 3  # precondition

    # Change the position of the Reply.
    reply_widget = cv.current_messages[reply.uuid]
    reply_widget.index = 1

    # add the new message and persist
    new_message = factory.Message(filename='4-source-msg.gpg', source=source)
    session.add(new_message)
    session.commit()

    cv.update_conversation(cv.source.collection)
    assert cv.conversation_layout.count() == 4
    assert reply_widget.index == 2  # re-ordered.


def test_update_conversation_content_updates(mocker, session):
    """
    Subsequent calls to update_conversation update the content of the conversation_item
    if it has changed.
    """
    mock_controller = mocker.MagicMock()
    # The controller's session must be a legitimate sqlalchemy session for this test
    mock_controller.session = session
    source = factory.Source()
    session.add(source)
    session.commit()

    message = factory.Message(filename='2-source-msg.gpg', source=source, content=None)
    session.add(message)
    session.commit()

    cv = ConversationView(source, mock_controller)
    cv.current_messages = {}  # Reset!

    cv.conversation_layout.insertWidget = mocker.MagicMock()
    cv.conversation_layout.removeWidget = mocker.MagicMock()
    # this is the MessageWidget that __init__() would return
    mock_msg_widget_res = mocker.MagicMock()
    # mock MessageWidget so we can inspect the __init__ call to see what content
    # is in the widget.
    mock_msg_widget = mocker.patch('securedrop_client.gui.widgets.MessageWidget',
                                   return_value=mock_msg_widget_res)

    # First call of update_conversation: with null content
    cv.update_conversation(cv.source.collection)

    # Since the content was None, we should have created the widget
    # with the default message (which is the second call_arg).
    assert mock_msg_widget.call_args[0][1] == '<Message not yet available>'

    # Meanwhile, in another session, we add content to the database for that same message.
    engine = session.get_bind()
    second_session = scoped_session(sessionmaker(bind=engine))
    message = second_session.query(db.Message).one()
    expected_content = 'now there is content here!'
    message.content = expected_content
    second_session.add(message)
    second_session.commit()

    # Second call of update_conversation
    cv.update_conversation(cv.source.collection)

    # Check that the widget was updated with the expected content.
    assert mock_msg_widget_res.message.setText.call_args[0][0] == expected_content


def test_SourceProfileShortWidget_update_timestamp(mocker):
    """
    Ensure the update_timestamp slot actually updates the LastUpdatedLabel
    instance with the last_updated value from the source..
    """
    mock_controller = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    mock_source.last_updated = datetime.now()
    mock_source.journalist_designation = "wimple horse knackered unittest"
    spsw = SourceProfileShortWidget(mock_source, mock_controller)
    spsw.updated = mocker.MagicMock()
    spsw.update_timestamp()
    spsw.updated.setText.assert_called_once_with(
        arrow.get(mock_source.last_updated).format('DD MMM'))
