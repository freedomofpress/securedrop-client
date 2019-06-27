"""
Make sure the UI widgets are configured correctly and work as expected.
"""
from PyQt5.QtWidgets import QWidget, QApplication, QWidgetItem, QSpacerItem, QVBoxLayout, \
    QMessageBox, QMainWindow, QTextEdit
from PyQt5.QtCore import Qt
from sqlalchemy.orm import scoped_session, sessionmaker

from tests import factory
from securedrop_client import db, logic
from securedrop_client.gui.widgets import MainView, SourceList, SourceWidget, LoginDialog, \
    SpeechBubble, ConversationWidget, MessageWidget, ReplyWidget, FileWidget, ConversationView, \
    DeleteSourceMessageBox, DeleteSourceAction, SourceMenu, TopPane, LeftPane, RefreshButton, \
    ErrorStatusBar, ActivityStatusBar, UserProfile, UserButton, UserMenu, LoginButton, \
    ReplyBoxWidget, SourceConversationWrapper, StarToggleButton


app = QApplication([])


def test_TopPane_init(mocker):
    """
    Ensure the TopPane instance is correctly set up.
    """
    tp = TopPane()
    assert not tp.refresh.isEnabled()


def test_TopPane_setup(mocker):
    """
    Calling setup calls setup for RefreshButton.
    """
    tp = TopPane()
    tp.refresh = mocker.MagicMock()
    mock_controller = mocker.MagicMock()

    tp.setup(mock_controller)

    tp.refresh.setup.assert_called_once_with(mock_controller)


def test_TopPane_enable_refresh(mocker):
    """
    Calling enable_refresh calls enable on RefreshButton.
    """
    tp = TopPane()
    tp.refresh = mocker.MagicMock()

    tp.enable_refresh()

    tp.refresh.enable.assert_called_once_with()


def test_TopPane_disable_refresh(mocker):
    """
    Calling disable_refresh calls disable on RefreshButton.
    """
    tp = TopPane()
    tp.refresh = mocker.MagicMock()

    tp.disable_refresh()

    tp.refresh.disable.assert_called_once_with()


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
    Calling clear_error_status calls clear_message on RefreshButton.
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

    lp.set_logged_in_as('test')

    lp.user_profile.show.assert_called_once_with()
    lp.user_profile.set_username.assert_called_once_with('test')


def test_LeftPane_set_logged_out(mocker):
    """
    When a user is logged out check that buttons and menus are in the correct state.
    """
    lp = LeftPane()
    lp.user_profile = mocker.MagicMock()

    lp.set_logged_out()

    lp.user_profile.hide.assert_called_once_with()


def test_RefreshButton_setup(mocker):
    """
    Calling setup stores reference to controller, which will later be used to update button icon on
    sync event.
    """
    rb = RefreshButton()
    controller = mocker.MagicMock()

    rb.setup(controller)

    assert rb.controller == controller


def test_RefreshButton_on_clicked(mocker):
    """
    When refresh button is clicked, sync_api should be called.
    """
    rb = RefreshButton()
    rb.controller = mocker.MagicMock()

    rb._on_clicked()

    rb.controller.sync_api.assert_called_once_with()


def test_RefreshButton_on_refresh_complete(mocker):
    """
    Make sure we are enabled after a refresh completes.
    """
    rb = RefreshButton()
    rb._on_refresh_complete('synced')
    assert rb.isEnabled()


def test_RefreshButton_enable(mocker):
    rb = RefreshButton()
    rb.enable()
    assert rb.isEnabled()


def test_RefreshButton_disable(mocker):
    rb = RefreshButton()
    rb.disable()
    assert not rb.isEnabled()


def test_ErrorStatusBar_clear_error_status(mocker):
    """
    Calling clear_error_status calls clear_message on RefreshButton.
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


def test_UserProfile_set_username(mocker):
    up = UserProfile()
    up.user_icon = mocker.MagicMock()
    up.user_button = mocker.MagicMock()

    up.set_username('test_username')

    up.user_icon.setText.assert_called_once_with('jo')  # testing current behavior as placeholder
    up.user_button.set_username.assert_called_once_with('test_username')


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


def test_MainView_show_sources(mocker):
    """
    Ensure the sources list is passed to the source list widget to be updated.
    """
    mv = MainView(None)
    mv.source_list = mocker.MagicMock()

    mv.show_sources([1, 2, 3])

    mv.source_list.update.assert_called_once_with([1, 2, 3])


def test_MainView_on_source_changed(mocker):
    """
    Ensure set_conversation is called when source changes.
    """
    mv = MainView(None)
    mv.source_list = mocker.MagicMock()
    mv.set_conversation = mocker.MagicMock()
    source = factory.Source()
    mv.set_conversation.get_current_source = mocker.MagicMock(return_value=source)
    mv.controller = mocker.MagicMock(is_authenticated=True)
    mocker.patch('securedrop_client.gui.widgets.source_exists', return_value=True)
    scw = mocker.MagicMock()
    mocker.patch('securedrop_client.gui.widgets.SourceConversationWrapper', return_value=scw)

    mv.on_source_changed()

    mv.source_list.get_current_source.assert_called_once_with()
    mv.set_conversation.assert_called_once_with(scw)


def test_MainView_on_source_changed_when_source_no_longer_exists(mocker):
    """
    Test that conversation for a source is cleared when the source no longer exists.
    """
    mv = MainView(None)
    mv.clear_conversation = mocker.MagicMock()
    mv.controller = mocker.MagicMock(is_authenticated=True)
    mocker.patch('securedrop_client.gui.widgets.source_exists', return_value=False)

    mv.on_source_changed()

    mv.clear_conversation.assert_called_once_with()


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
    mv.source_list.get_current_source = mocker.MagicMock(return_value=s)
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
        'securedrop_client.gui.widgets.SourceConversationWrapper.__init__', return_value=None)

    # We expect on the first call, SourceConversationWrapper.__init__ should be called.
    mv.source_list.get_current_source = mocker.MagicMock(return_value=source)
    mv.on_source_changed()
    assert mv.set_conversation.call_count == 1
    assert source_conversation_init.call_count == 1

    # Reset mock call counts for next call of on_source_changed.
    source_conversation_init.reset_mock()
    mv.set_conversation.reset_mock()

    # Now click on another source (source2). Since this is the first time we have clicked
    # on source2, we expect on the first call, SourceConversationWrapper.__init__ should be
    # called.
    mv.source_list.get_current_source = mocker.MagicMock(return_value=source2)
    mv.on_source_changed()
    assert mv.set_conversation.call_count == 1
    assert source_conversation_init.call_count == 1

    # Reset mock call counts for next call of on_source_changed.
    source_conversation_init.reset_mock()
    mv.set_conversation.reset_mock()

    # But if we click back (call on_source_changed again) to the source,
    # its SourceConversationWrapper should _not_ be recreated.
    mv.source_list.get_current_source = mocker.MagicMock(return_value=source)
    mv.on_source_changed()
    assert mv.set_conversation.call_count == 1
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


def test_MainView_clear_conversation(mocker, homedir):
    """
    Calling clear_conversation deletes items from layout
    """
    mv = MainView(None)
    mv.view_layout = QVBoxLayout()
    mv.view_layout.addWidget(QWidget())

    assert mv.view_layout.count() == 1

    mv.clear_conversation()

    assert mv.view_layout.count() == 0


def test_SourceList_update(mocker):
    """
    Check the items in the source list are cleared and a new SourceWidget for
    each passed-in source is created along with an associated QListWidgetItem.
    """
    sl = SourceList()

    sl.clear = mocker.MagicMock()
    sl.addItem = mocker.MagicMock()
    sl.setItemWidget = mocker.MagicMock()
    sl.controller = mocker.MagicMock()

    mock_sw = mocker.MagicMock()
    mock_lwi = mocker.MagicMock()
    mocker.patch('securedrop_client.gui.widgets.SourceWidget', mock_sw)
    mocker.patch('securedrop_client.gui.widgets.QListWidgetItem', mock_lwi)

    sources = [mocker.MagicMock(), mocker.MagicMock(), mocker.MagicMock(), ]
    sl.update(sources)

    sl.clear.assert_called_once_with()
    assert mock_sw.call_count == len(sources)
    assert mock_lwi.call_count == len(sources)
    assert sl.addItem.call_count == len(sources)
    assert sl.setItemWidget.call_count == len(sources)


def test_SourceList_maintains_selection(mocker):
    """
    Maintains the selected item if present in new list
    """
    sl = SourceList()
    sources = [factory.Source(), factory.Source()]
    sl.setup(mocker.MagicMock())
    sl.update(sources)

    sl.setCurrentItem(sl.itemAt(0, 0))
    sl.update(sources)

    assert sl.currentItem()
    assert sl.itemWidget(sl.currentItem()).source.id == sources[0].id


def test_SourceWidget_init(mocker):
    """
    The source widget is initialised with the passed-in source.
    """
    mock_source = mocker.MagicMock()
    mock_source.journalist_designation = 'foo bar baz'
    sw = SourceWidget(mock_source)
    assert sw.source == mock_source


def test_SourceWidget_setup(mocker):
    """
    The setup method adds the controller as an attribute on the SourceWidget.
    """
    mock_controller = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    sw = SourceWidget(mock_source)
    sw.star = mocker.MagicMock()

    sw.setup(mock_controller)

    assert sw.controller == mock_controller
    sw.star.setup.assert_called_once_with(mock_controller)


def test_SourceWidget_html_init(mocker):
    """
    The source widget is initialised with the given source name, with
    HTML escaped properly.
    """
    mock_source = mocker.MagicMock()
    mock_source.journalist_designation = 'foo <b>bar</b> baz'

    sw = SourceWidget(mock_source)
    sw.name = mocker.MagicMock()
    sw.summary_layout = mocker.MagicMock()

    mocker.patch('securedrop_client.gui.SvgLabel')
    sw.update()

    sw.name.setText.assert_called_once_with('<strong>foo &lt;b&gt;bar&lt;/b&gt; baz</strong>')


def test_SourceWidget_update_attachment_icon():
    """
    Attachment icon identicates document count
    """
    source = factory.Source(document_count=1)
    sw = SourceWidget(source)

    sw.update()
    assert not sw.attached.isHidden()

    source.document_count = 0

    sw.update()
    assert sw.attached.isHidden()


def test_SourceWidget_delete_source(mocker, session, source):
    mock_delete_source_message_box_object = mocker.MagicMock(DeleteSourceMessageBox)
    mock_controller = mocker.MagicMock()
    mock_delete_source_message = mocker.MagicMock(
        return_value=mock_delete_source_message_box_object)

    sw = SourceWidget(source['source'])
    sw.controller = mock_controller

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
    sw = SourceWidget(source)
    sw.controller = mock_controller

    mocker.patch(
        "securedrop_client.gui.widgets.QMessageBox.question",
        mock_message_box_question,
    )
    sw.delete_source(None)
    sw.controller.delete_source.assert_not_called()


def test_StarToggleButton_init_source_starred(mocker):
    source = factory.Source()
    source.is_starred = True

    stb = StarToggleButton(source)

    assert stb.source == source
    assert stb.isChecked() is True


def test_StarToggleButton_init_source_unstarred(mocker):
    source = factory.Source()
    source.is_starred = False

    stb = StarToggleButton(source)

    assert stb.source == source
    assert stb.isChecked() is False


def test_StarToggleButton_setup(mocker):
    star_toggle_button = StarToggleButton(source=mocker.MagicMock())
    controller = mocker.MagicMock()
    controller.authentication_state = mocker.MagicMock()
    controller.is_authenticated = 'mock'
    on_authentication_changed_fn = mocker.patch.object(
        StarToggleButton, 'on_authentication_changed')

    star_toggle_button.setup(controller)

    assert star_toggle_button.controller == controller
    controller.authentication_state.connect.assert_called_once_with(on_authentication_changed_fn)
    on_authentication_changed_fn.assert_called_with('mock')


def test_StarToggleButton_on_authentication_changed_while_authenticated_and_checked(mocker):
    """
    If on_authentication_changed is set up correctly, then calling toggle on a checked button should
    result in the button being unchecked.
    """
    source = mocker.MagicMock()
    stb = StarToggleButton(source=source)
    stb.setChecked(True)
    stb.on_toggle = mocker.MagicMock()
    stb.on_authentication_changed(authenticated=True)

    stb.toggle()

    assert stb.on_toggle.called is True
    assert stb.isChecked() is False


def test_StarToggleButton_on_authentication_changed_while_authenticated_and_not_checked(mocker):
    """
    If on_authentication_changed is set up correctly, then calling toggle on an unchecked button
    should result in the button being unchecked.
    """
    source = mocker.MagicMock()
    stb = StarToggleButton(source=source)
    stb.setChecked(False)
    stb.on_toggle = mocker.MagicMock()
    stb.on_authentication_changed(authenticated=True)

    stb.toggle()

    assert stb.on_toggle.called is True
    assert stb.isChecked() is True


def test_StarToggleButton_on_authentication_changed_while_offline_mode(mocker):
    """
    Ensure on_authentication_changed is set up correctly for offline mode.
    """
    source = mocker.MagicMock()
    stb = StarToggleButton(source=source)
    stb.on_toggle_offline = mocker.MagicMock()
    stb.on_toggle = mocker.MagicMock()

    stb.on_authentication_changed(authenticated=False)
    stb.click()

    assert stb.on_toggle_offline.called is True
    assert stb.on_toggle.called is False


def test_StarToggleButton_on_toggle(mocker):
    """
    Ensure correct star icon images are loaded for the enabled button.
    """
    source = mocker.MagicMock()
    stb = StarToggleButton(source)
    stb.controller = mocker.MagicMock()

    stb.on_toggle()

    stb.controller.update_star.assert_called_once_with(source)
    assert stb.isCheckable() is True


def test_StarToggleButton_on_toggle_offline(mocker):
    """
    Ensure toggle is disabled when offline.
    """
    source = mocker.MagicMock()
    stb = StarToggleButton(source)
    stb.controller = mocker.MagicMock()

    stb.on_toggle_offline()

    stb.controller.on_action_requiring_login.assert_called_once_with()
    assert stb.isCheckable() is False


def test_StarToggleButton_on_toggle_offline_when_checked(mocker):
    """
    Ensure correct star icon images are loaded for the disabled button.
    """
    source = mocker.MagicMock()
    source.is_starred = True
    stb = StarToggleButton(source)
    stb.controller = mocker.MagicMock()
    set_icon_fn = mocker.patch('securedrop_client.gui.SvgToggleButton.set_icon')
    stb.on_toggle_offline()

    stb.controller.on_action_requiring_login.assert_called_once_with()
    assert stb.isCheckable() is False
    set_icon_fn.assert_called_with(on='star_on.svg', off='star_on.svg')


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
    ld.error_label = mocker.MagicMock()

    ld.reset()

    ld.username_field.setText.assert_called_once_with('')
    ld.password_field.setText.assert_called_once_with('')
    ld.tfa_field.setText.assert_called_once_with('')
    ld.setDisabled.assert_called_once_with(False)
    ld.error_label.setText.assert_called_once_with('')


def test_LoginDialog_error(mocker, i18n):
    """
    Any error message passed in is assigned as the text for the error label.
    """
    mock_controller = mocker.MagicMock()
    ld = LoginDialog(None)
    ld.setup(mock_controller)
    ld.error_label = mocker.MagicMock()
    ld.error('foo')
    ld.error_label.setText.assert_called_once_with('foo')


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


def test_LoginDialog_keyPressEvent(mocker):
    """
    Ensure we don't hide the login dialog when Esc key is pressed.
    """
    ld = LoginDialog(None)
    event = mocker.MagicMock()
    event.key = mocker.MagicMock(return_value=Qt.Key_Escape)

    ld.keyPressEvent(event)

    event.ignore.assert_called_once_with()


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
    mock_label = mocker.patch('securedrop_client.gui.widgets.QLabel')
    mocker.patch('securedrop_client.gui.widgets.QVBoxLayout')
    mocker.patch('securedrop_client.gui.widgets.SpeechBubble.setLayout')
    mock_signal = mocker.Mock()
    mock_connect = mocker.Mock()
    mock_signal.connect = mock_connect

    SpeechBubble('mock id', 'hello', mock_signal)
    mock_label.assert_called_once_with('hello')
    assert mock_connect.called


def test_SpeechBubble_update_text(mocker):
    """
    Check that the calling the slot updates the text.
    """
    mocker.patch('securedrop_client.gui.widgets.QVBoxLayout')
    mocker.patch('securedrop_client.gui.widgets.SpeechBubble.setLayout')
    mock_signal = mocker.MagicMock()

    msg_id = 'abc123'
    sb = SpeechBubble(msg_id, 'hello', mock_signal)

    new_msg = 'new message'
    sb._update_text(msg_id, new_msg)
    assert sb.message.text() == new_msg

    newer_msg = 'an even newer message'
    sb._update_text(msg_id + 'xxxxx', newer_msg)
    assert sb.message.text() == new_msg


def test_SpeechBubble_html_init(mocker):
    """
    Check the speech bubble is configured correctly (there's a label containing
    the passed in text, with HTML escaped properly).
    """
    mock_label = mocker.patch('securedrop_client.gui.widgets.QLabel')
    mocker.patch('securedrop_client.gui.widgets.QVBoxLayout')
    mocker.patch('securedrop_client.gui.widgets.SpeechBubble.setLayout')
    mock_signal = mocker.MagicMock()

    SpeechBubble('mock id', '<b>hello</b>', mock_signal)
    mock_label.assert_called_once_with('&lt;b&gt;hello&lt;/b&gt;')


def test_SpeechBubble_with_apostrophe_in_text(mocker):
    """Check Speech Bubble is displaying text with apostrophe correctly."""
    mock_label = mocker.patch('securedrop_client.gui.widgets.QLabel')
    mocker.patch('securedrop_client.gui.widgets.QVBoxLayout')
    mocker.patch('securedrop_client.gui.widgets.SpeechBubble.setLayout')
    mock_signal = mocker.MagicMock()

    message = "I'm sure, you are reading my message."
    SpeechBubble('mock id', message, mock_signal)
    mock_label.assert_called_once_with(message)


def test_ConversationWidget_init_left(mocker):
    """
    Check the ConversationWidget is configured correctly for align-left.
    """
    mock_signal = mocker.Mock()
    mock_connect = mocker.Mock()
    mock_signal.connect = mock_connect

    cw = ConversationWidget('mock id', 'hello', mock_signal, align='left')
    layout = cw.layout()

    assert isinstance(layout.takeAt(0), QWidgetItem)
    assert isinstance(layout.takeAt(0), QSpacerItem)
    assert mock_connect.called


def test_ConversationWidget_init_right(mocker):
    """
    Check the ConversationWidget is configured correctly for align-left.
    """
    mock_signal = mocker.Mock()
    mock_connect = mocker.Mock()
    mock_signal.connect = mock_connect

    cw = ConversationWidget('mock id', 'hello', mock_signal, align='right')
    layout = cw.layout()

    assert isinstance(layout.takeAt(0), QSpacerItem)
    assert isinstance(layout.takeAt(0), QWidgetItem)
    assert mock_connect.called


def test_MessageWidget_init(mocker):
    """
    Check the CSS is set as expected.
    """
    mock_signal = mocker.Mock()
    mock_connected = mocker.Mock()
    mock_signal.connect = mock_connected

    mw = MessageWidget('mock id', 'hello', mock_signal)
    ss = mw.styleSheet()

    assert 'background-color' in ss
    assert mock_connected.called


def test_ReplyWidget_init(mocker):
    """
    Check the CSS is set as expected.
    """
    mock_update_signal = mocker.Mock()
    mock_update_connected = mocker.Mock()
    mock_update_signal.connect = mock_update_connected

    mock_success_signal = mocker.MagicMock()
    mock_success_connected = mocker.Mock()
    mock_success_signal.connect = mock_success_connected

    mock_failure_signal = mocker.MagicMock()
    mock_failure_connected = mocker.Mock()
    mock_failure_signal.connect = mock_failure_connected

    rw = ReplyWidget(
        'mock id',
        'hello',
        mock_update_signal,
        mock_success_signal,
        mock_failure_signal,
    )
    ss = rw.styleSheet()

    assert 'background-color' in ss
    assert mock_update_connected.called
    assert mock_success_connected.called
    assert mock_failure_connected.called


def test_FileWidget_init_left(mocker):
    """
    Check the FileWidget is configured correctly for align-left.
    """
    mock_controller = mocker.MagicMock()
    mock_signal = mocker.MagicMock()  # not important for this test
    mock_uuid = 'mock'

    fw = FileWidget(mock_uuid, mock_controller, mock_signal)

    assert isinstance(fw.layout.takeAt(0), QWidgetItem)
    assert isinstance(fw.layout.takeAt(0), QWidgetItem)
    assert isinstance(fw.layout.takeAt(0), QSpacerItem)
    assert fw.controller == mock_controller


def test_FileWidget_mousePressEvent_download(mocker, session, source):
    """
    Should fire the expected download event handler in the logic layer.
    """
    mock_signal = mocker.MagicMock()  # not important for this test

    file_ = factory.File(source=source['source'],
                         is_downloaded=False,
                         is_decrypted=None)
    session.add(file_)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file_)
    mock_controller = mocker.MagicMock(get_file=mock_get_file)

    fw = FileWidget(file_.uuid, mock_controller, mock_signal)
    mock_get_file.assert_called_once_with(file_.uuid)
    mock_get_file.reset_mock()

    fw.mouseReleaseEvent(None)
    mock_get_file.assert_called_once_with(file_.uuid)
    mock_controller.on_submission_download.assert_called_once_with(
        db.File, file_.uuid)


def test_FileWidget_mousePressEvent_open(mocker, session, source):
    """
    Should fire the expected open event handler in the logic layer.
    """
    mock_signal = mocker.MagicMock()  # not important for this test

    file_ = factory.File(source=source['source'], is_downloaded=True)
    session.add(file_)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file_)
    mock_controller = mocker.MagicMock(get_file=mock_get_file)

    fw = FileWidget(file_.uuid, mock_controller, mock_signal)
    fw.mouseReleaseEvent(None)
    fw.controller.on_file_open.assert_called_once_with(file_.uuid)


def test_FileWidget_clear_deletes_items(mocker, session, source):
    """
    Calling the clear() method on FileWidget should delete the existing items in the layout.
    """
    mock_signal = mocker.MagicMock()  # not important for this test

    file_ = factory.File(source=source['source'], is_downloaded=True)
    session.add(file_)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file_)
    mock_controller = mocker.MagicMock(get_file=mock_get_file)

    fw = FileWidget(file_.uuid, mock_controller, mock_signal)
    assert fw.layout.count() != 0

    fw.clear()

    assert fw.layout.count() == 0


def test_FileWidget_on_file_download_updates_items_when_uuid_matches(mocker, source, session):
    """
    The _on_file_download method should clear and update the FileWidget
    """
    mock_signal = mocker.MagicMock()  # not important for this test

    file_ = factory.File(source=source['source'], is_downloaded=True)
    session.add(file_)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file_)
    mock_controller = mocker.MagicMock(get_file=mock_get_file)

    fw = FileWidget(file_.uuid, mock_controller, mock_signal)
    fw.clear = mocker.MagicMock()
    fw.update = mocker.MagicMock()

    fw._on_file_downloaded(file_.uuid)

    fw.clear.assert_called_once_with()
    fw.update.assert_called_once_with()


def test_FileWidget_on_file_download_updates_items_when_uuid_does_not_match(
    mocker, homedir, session, source,
):
    """
    The _on_file_download method should clear and update the FileWidget
    """
    mock_signal = mocker.MagicMock()  # not important for this test

    file_ = factory.File(source=source['source'], is_downloaded=True)
    session.add(file_)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file_)
    mock_controller = mocker.MagicMock(get_file=mock_get_file)

    fw = FileWidget(file_.uuid, mock_controller, mock_signal)
    fw.clear = mocker.MagicMock()
    fw.update = mocker.MagicMock()

    fw._on_file_downloaded('not a matching uuid')

    fw.clear.assert_not_called()
    fw.update.assert_not_called()


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
    it is following the conversation.
    """
    mocked_source = mocker.MagicMock()
    mocked_controller = mocker.MagicMock()

    cv = ConversationView(mocked_source, mocked_controller)

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
    mocked_controller = mocker.MagicMock(session=session, message_ready=mock_message_ready_signal)

    content = 'a sea, a bee'
    message = factory.Message(source=source, content=content)
    session.add(message)
    session.commit()

    cv = ConversationView(source, mocked_controller)
    cv.conversation_layout = mocker.MagicMock()
    # this is the MessageWidget that __init__() would return
    mock_msg_widget_res = mocker.MagicMock()
    # mock the actual MessageWidget so we can inspect the __init__ call
    mock_msg_widget = mocker.patch('securedrop_client.gui.widgets.MessageWidget',
                                   return_value=mock_msg_widget_res)

    cv.add_message(message)

    # check that we built the widget was called with the correct args
    mock_msg_widget.assert_called_once_with(message.uuid, content, mock_message_ready_signal)

    # check that we added the correct widget to the layout
    cv.conversation_layout.addWidget.assert_called_once_with(mock_msg_widget_res)


def test_ConversationView_add_message_no_content(mocker, session, source):
    """
    Adding a message results in a new MessageWidget added to the layout. This case specifically
    checks that if a `Message` has `content = None` that a helpful message is displayed as would
    be the case if download/decryption never occurred or failed.
    """
    source = source['source']  # grab the source from the fixture dict for simplicity

    mock_message_ready_signal = mocker.MagicMock()
    mocked_controller = mocker.MagicMock(session=session, message_ready=mock_message_ready_signal)

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

    cv.add_message(message)

    # check that we built the widget was called with the correct args
    mock_msg_widget.assert_called_once_with(
        message.uuid, '<Message not yet available>', mock_message_ready_signal)

    # check that we added the correct widget to the layout
    cv.conversation_layout.addWidget.assert_called_once_with(mock_msg_widget_res)


def test_ConversationView_on_reply_sent(mocker):
    """
    The handler for new replies should call add_reply
    """
    source = factory.Source()
    controller = mocker.MagicMock()
    cv = ConversationView(source, controller)
    cv.add_reply_from_reply_box = mocker.MagicMock()

    cv.on_reply_sent(source.uuid, 'abc123', 'test message')

    cv.add_reply_from_reply_box.assert_called_with('abc123', 'test message')


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
    reply_succeeded = mocker.MagicMock()
    reply_failed = mocker.MagicMock()
    controller = mocker.MagicMock(
        reply_ready=reply_ready, reply_succeeded=reply_succeeded, reply_failed=reply_failed)
    cv = ConversationView(source, controller)
    cv.conversation_layout = mocker.MagicMock()
    reply_widget_res = mocker.MagicMock()
    reply_widget = mocker.patch(
        'securedrop_client.gui.widgets.ReplyWidget', return_value=reply_widget_res)

    cv.add_reply_from_reply_box('abc123', 'test message')

    reply_widget.assert_called_once_with(
        'abc123', 'test message', reply_ready, reply_succeeded, reply_failed)
    cv.conversation_layout.addWidget.assert_called_once_with(reply_widget_res)


def test_ConversationView_add_reply(mocker, session, source):
    """
    Adding a reply from a source results in a new ReplyWidget added to the layout.
    """
    source = source['source']  # grab the source from the fixture dict for simplicity

    mock_reply_ready_signal = mocker.MagicMock()
    mock_reply_succeeded_signal = mocker.MagicMock()
    mock_reply_failed_signal = mocker.MagicMock()
    mocked_controller = mocker.MagicMock(session=session,
                                         reply_ready=mock_reply_ready_signal,
                                         reply_succeeded=mock_reply_succeeded_signal,
                                         reply_failed=mock_reply_failed_signal)

    content = 'a sea, a bee'
    reply = factory.Reply(source=source, content=content)
    session.add(reply)
    session.commit()

    cv = ConversationView(source, mocked_controller)
    cv.conversation_layout = mocker.MagicMock()
    # this is the Reply that __init__() would return
    mock_reply_widget_res = mocker.MagicMock()
    # mock the actual MessageWidget so we can inspect the __init__ call
    mock_reply_widget = mocker.patch('securedrop_client.gui.widgets.ReplyWidget',
                                     return_value=mock_reply_widget_res)

    cv.add_reply(reply)

    # check that we built the widget was called with the correct args
    mock_reply_widget.assert_called_once_with(
        reply.uuid,
        content,
        mock_reply_ready_signal,
        mock_reply_succeeded_signal,
        mock_reply_failed_signal)

    # check that we added the correct widget to the layout
    cv.conversation_layout.addWidget.assert_called_once_with(mock_reply_widget_res)


def test_ConversationView_add_reply_no_content(mocker, session, source):
    """
    Adding a reply results in a new ReplyWidget added to the layout. This case specifically
    checks that if a `Reply` has `content = None` that a helpful message is displayed as would
    be the case if download/decryption never occurred or failed.
    """
    source = source['source']  # grab the source from the fixture dict for simplicity

    mock_reply_ready_signal = mocker.MagicMock()
    mock_reply_succeeded_signal = mocker.MagicMock()
    mock_reply_failed_signal = mocker.MagicMock()
    mocked_controller = mocker.MagicMock(session=session,
                                         reply_ready=mock_reply_ready_signal,
                                         reply_succeeded=mock_reply_succeeded_signal,
                                         reply_failed=mock_reply_failed_signal)

    reply = factory.Reply(source=source, is_decrypted=False, content=None)
    session.add(reply)
    session.commit()

    cv = ConversationView(source, mocked_controller)
    cv.conversation_layout = mocker.MagicMock()
    # this is the Reply that __init__() would return
    mock_reply_widget_res = mocker.MagicMock()
    # mock the actual MessageWidget so we can inspect the __init__ call
    mock_reply_widget = mocker.patch('securedrop_client.gui.widgets.ReplyWidget',
                                     return_value=mock_reply_widget_res)

    cv.add_reply(reply)

    # check that we built the widget was called with the correct args
    mock_reply_widget.assert_called_once_with(
        reply.uuid,
        '<Reply not yet available>',
        mock_reply_ready_signal,
        mock_reply_succeeded_signal,
        mock_reply_failed_signal)

    # check that we added the correct widget to the layout
    cv.conversation_layout.addWidget.assert_called_once_with(mock_reply_widget_res)


def test_ConversationView_add_downloaded_file(mocker, homedir):
    """
    Adding a file results in a new FileWidget added to the layout with the
    proper QLabel.
    """
    mocked_source = mocker.MagicMock()
    mocked_controller = mocker.MagicMock()

    cv = ConversationView(mocked_source, mocked_controller)
    cv.conversation_layout = mocker.MagicMock()

    mock_source = mocker.MagicMock()
    mock_file = mocker.MagicMock()
    mock_file.is_downloaded = True
    mock_label = mocker.patch('securedrop_client.gui.widgets.QLabel')
    mocker.patch('securedrop_client.gui.widgets.QHBoxLayout.addWidget')
    mocker.patch('securedrop_client.gui.widgets.FileWidget.setLayout')

    cv.add_file(mock_source, mock_file)
    mock_label.assert_called_with("Open")
    assert cv.conversation_layout.addWidget.call_count == 1

    cal = cv.conversation_layout.addWidget.call_args_list
    assert isinstance(cal[0][0][0], FileWidget)


def test_ConversationView_add_not_downloaded_file(mocker, homedir, source, session):
    """
    Adding a file results in a new FileWidget added to the layout with the
    proper QLabel.
    """
    file_ = factory.File(source=source['source'],
                         is_downloaded=False,
                         is_decrypted=None,
                         size=123)
    session.add(file_)
    session.commit()

    mock_get_file = mocker.MagicMock(return_value=file_)
    mocked_controller = mocker.MagicMock(get_file=mock_get_file)

    cv = ConversationView(source['source'], mocked_controller)
    cv.conversation_layout = mocker.MagicMock()

    mock_label = mocker.patch('securedrop_client.gui.widgets.QLabel')
    mocker.patch('securedrop_client.gui.widgets.QHBoxLayout.addWidget')
    mocker.patch('securedrop_client.gui.widgets.FileWidget.setLayout')

    cv.add_file(source['source'], file_)
    mock_label.assert_called_with("Download (123 bytes)")
    assert cv.conversation_layout.addWidget.call_count == 1

    cal = cv.conversation_layout.addWidget.call_args_list
    assert isinstance(cal[0][0][0], FileWidget)


def test_DeleteSourceMessageBox_init(mocker, source):
    mock_controller = mocker.MagicMock()
    DeleteSourceMessageBox(None, source['source'], mock_controller)


def test_DeleteSourceMessage_launch_when_user_chooses_cancel(mocker, source):
    source = source['source']  # to get the Source object

    mock_message_box_question = mocker.MagicMock(QMessageBox.question)
    mock_message_box_question.return_value = QMessageBox.Cancel
    mock_controller = mocker.MagicMock()

    delete_source_message_box = DeleteSourceMessageBox(None, source, mock_controller)

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

    delete_source_message_box = DeleteSourceMessageBox(None, source, mock_controller)

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

    delete_source_message_box = DeleteSourceMessageBox(None, source, mock_controller)

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
    mock_source = mocker.MagicMock()
    mock_controller = mocker.MagicMock(logic.Controller)
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
        source_widget = SourceWidget(mock_source)
        source_widget.setup(mock_controller)
        source_widget.delete_source(mock_event)
        mock_delete_source_message_box_obj.launch.assert_not_called()


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
    scw.reply_box.text_edit = QTextEdit('Alles für Alle')

    scw.reply_box.send_reply()

    scw.reply_box.reply_sent.emit.assert_called_once_with('abc123', '456xyz', 'Alles für Alle')
    assert scw.reply_box.text_edit.toPlainText() == ''
    controller.send_reply.assert_called_once_with('abc123', '456xyz', 'Alles für Alle')


def test_ReplyBoxWidget_send_reply_does_not_send_empty_string(mocker):
    """
    Ensure sending a reply from the reply box does not send empty string.
    """
    source = mocker.MagicMock()
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.text_edit = QTextEdit()
    assert not rb.text_edit.toPlainText()

    rb.send_reply()

    assert not controller.send_reply.called

    # Also check that we don't send blank space
    rb.text_edit.setText('  \n\n  ')

    rb.send_reply()

    assert not controller.send_reply.called


def test_ReplyWidget_success_failure_slots(mocker):
    mock_update_signal = mocker.Mock()
    mock_success_signal = mocker.Mock()
    mock_failure_signal = mocker.Mock()
    msg_id = 'abc123'

    widget = ReplyWidget(msg_id,
                         'lol',
                         mock_update_signal,
                         mock_success_signal,
                         mock_failure_signal)

    # ensure we have connected the slots
    mock_success_signal.connect.assert_called_once_with(widget._on_reply_success)
    mock_failure_signal.connect.assert_called_once_with(widget._on_reply_failure)
    assert mock_update_signal.connect.called  # to ensure no stale mocks

    # check the success slog
    mock_logger = mocker.patch('securedrop_client.gui.widgets.logger')
    widget._on_reply_success(msg_id + "x")
    assert not mock_logger.debug.called
    widget._on_reply_success(msg_id)
    assert mock_logger.debug.called
    mock_logger.reset_mock()

    # check the failure slot
    mock_logger = mocker.patch('securedrop_client.gui.widgets.logger')
    widget._on_reply_failure(msg_id + "x")
    assert not mock_logger.debug.called
    widget._on_reply_failure(msg_id)
    assert mock_logger.debug.called


def test_ReplyBoxWidget__on_authentication_changed(mocker, homedir):
    """
    When the client is authenticated, enable reply box.
    """
    source = mocker.MagicMock()
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.enable = mocker.MagicMock()

    rb._on_authentication_changed(True)

    rb.enable.assert_called_once_with()


def test_ReplyBoxWidget__on_authentication_changed_offline(mocker, homedir):
    """
    When the client goes offline, disable reply box.
    """
    source = mocker.MagicMock()
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.disable = mocker.MagicMock()

    rb._on_authentication_changed(False)

    rb.disable.assert_called_once_with()


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
    _on_authentication_changed_fn.assert_called_with(controller.is_authenticated)


def test_ReplyBoxWidget_enable(mocker):
    source = mocker.MagicMock()
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.text_edit = QTextEdit()
    rb.send_button = mocker.MagicMock()

    rb.enable()

    assert rb.text_edit.isEnabled()
    assert rb.text_edit.toPlainText() == ''
    rb.send_button.show.assert_called_once_with()


def test_ReplyBoxWidget_disable(mocker):
    source = mocker.MagicMock()
    controller = mocker.MagicMock()
    rb = ReplyBoxWidget(source, controller)
    rb.text_edit = QTextEdit()
    rb.send_button = mocker.MagicMock()

    rb.disable()

    assert not rb.text_edit.isEnabled()
    assert rb.text_edit.toPlainText() == 'You need to log in to send replies.'
    rb.send_button.hide.assert_called_once_with()


def test_update_conversation_maintains_old_items(mocker, session):
    """
    Calling update_conversation deletes and adds old items back to layout
    """
    mock_controller = mocker.MagicMock()
    source = factory.Source()
    session.add(source)
    session.flush()

    file_ = factory.File(filename='1-source-doc.gpg', source=source)
    session.add(file_)
    message = factory.Message(filename='2-source-msg.gpg', source=source)
    session.add(message)
    reply = factory.Reply(filename='3-source-reply.gpg', source=source)
    session.add(reply)
    session.commit()

    cv = ConversationView(source, mock_controller)
    assert cv.conversation_layout.count() == 3

    cv.update_conversation(cv.source.collection)

    assert cv.conversation_layout.count() == 3


def test_update_conversation_adds_new_items(mocker, session):
    """
    Calling update_conversation adds new items to layout
    """
    mock_controller = mocker.MagicMock()
    source = factory.Source()
    session.add(source)
    session.flush()

    file_ = factory.File(filename='1-source-doc.gpg', source=source)
    session.add(file_)
    message = factory.Message(filename='2-source-msg.gpg', source=source)
    session.add(message)
    reply = factory.Reply(filename='3-source-reply.gpg', source=source)
    session.add(reply)
    session.commit()

    cv = ConversationView(source, mock_controller)
    assert cv.conversation_layout.count() == 3  # precondition

    # add the new message and persist
    new_message = factory.Message(filename='4-source-msg.gpg', source=source)
    session.add(new_message)
    session.commit()

    cv.update_conversation(cv.source.collection)
    assert cv.conversation_layout.count() == 4


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
    session.flush()

    message = factory.Message(filename='2-source-msg.gpg', source=source, content=None)
    session.add(message)
    session.commit()

    cv = ConversationView(source, mock_controller)

    cv.conversation_layout.addWidget = mocker.MagicMock()
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
    assert mock_msg_widget.call_args[0][1] == expected_content


def test_clear_conversation_deletes_items(mocker, homedir):
    """
    Calling clear_conversation deletes items from layout
    """
    mock_controller = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    message = db.Message(uuid='uuid', content='message', filename='1-foo')
    cv = ConversationView(mock_source, mock_controller)
    cv.add_message(message)
    assert cv.conversation_layout.count() == 1

    cv.clear_conversation()

    assert cv.conversation_layout.count() == 0
