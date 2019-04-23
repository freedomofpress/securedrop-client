"""
Make sure the UI widgets are configured correctly and work as expected.
"""
from PyQt5.QtWidgets import QWidget, QApplication, QWidgetItem, QSpacerItem, QVBoxLayout, \
    QMessageBox, QLabel, QMainWindow
from PyQt5.QtCore import Qt

from tests import factory
from securedrop_client import db, logic
from securedrop_client.gui.widgets import MainView, SourceList, SourceWidget, LoginDialog, \
    SpeechBubble, ConversationWidget, MessageWidget, ReplyWidget, FileWidget, ConversationView, \
    DeleteSourceMessageBox, DeleteSourceAction, SourceMenu, TopPane, LeftPane, RefreshButton, \
    ErrorStatusBar, ActivityStatusBar, UserProfile, UserButton, UserMenu, LoginButton, \
    ReplyBoxWidget, SourceConversationWrapper


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


def test_MainView_show_conversation(mocker):
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
    sl = SourceList(None)

    sl.clear = mocker.MagicMock()
    sl.addItem = mocker.MagicMock()
    sl.setItemWidget = mocker.MagicMock()
    sl.controller = mocker.MagicMock()

    mock_sw = mocker.MagicMock()
    mock_lwi = mocker.MagicMock()
    mocker.patch('securedrop_client.gui.widgets.SourceWidget', mock_sw)
    mocker.patch('securedrop_client.gui.widgets.QListWidgetItem', mock_lwi)

    sources = ['a', 'b', 'c', ]
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
    sl = SourceList(None)
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
    sw = SourceWidget(None, mock_source)
    assert sw.source == mock_source


def test_SourceWidget_setup(mocker):
    """
    The setup method adds the controller as an attribute on the SourceWidget.
    """
    mock_controller = mocker.MagicMock()
    mock_source = mocker.MagicMock()

    sw = SourceWidget(None, mock_source)
    sw.setup(mock_controller)

    assert sw.controller == mock_controller


def test_SourceWidget_html_init(mocker):
    """
    The source widget is initialised with the given source name, with
    HTML escaped properly.
    """
    mock_source = mocker.MagicMock()
    mock_source.journalist_designation = 'foo <b>bar</b> baz'

    sw = SourceWidget(None, mock_source)
    sw.name = mocker.MagicMock()
    sw.summary_layout = mocker.MagicMock()

    mocker.patch('securedrop_client.gui.widgets.load_svg')
    sw.update()

    sw.name.setText.assert_called_once_with('<strong>foo &lt;b&gt;bar&lt;/b&gt; baz</strong>')


def test_SourceWidget_update_starred(mocker):
    """
    Ensure the widget displays the expected details from the source.
    """
    mock_source = mocker.MagicMock()
    mock_source.journalist_designation = 'foo bar baz'
    mock_source.is_starred = True

    sw = SourceWidget(None, mock_source)
    sw.name = mocker.MagicMock()
    sw.summary_layout = mocker.MagicMock()

    mock_load = mocker.patch('securedrop_client.gui.widgets.load_svg')
    sw.update()

    mock_load.assert_called_once_with('star_on.svg')
    sw.name.setText.assert_called_once_with('<strong>foo bar baz</strong>')


def test_SourceWidget_update_unstarred(mocker):
    """
    Ensure the widget displays the expected details from the source.
    """
    mock_source = mocker.MagicMock()
    mock_source.journalist_designation = 'foo bar baz'
    mock_source.is_starred = False

    sw = SourceWidget(None, mock_source)
    sw.name = mocker.MagicMock()
    sw.summary_layout = mocker.MagicMock()

    mock_load = mocker.patch('securedrop_client.gui.widgets.load_svg')
    sw.update()

    mock_load.assert_called_once_with('star_off.svg')
    sw.name.setText.assert_called_once_with('<strong>foo bar baz</strong>')


def test_SourceWidget_update_attachment_icon():
    """
    Attachment icon identicates document count
    """
    source = factory.Source(document_count=1)
    sw = SourceWidget(None, source)

    sw.update()
    assert not sw.attached.isHidden()

    source.document_count = 0

    sw.update()
    assert sw.attached.isHidden()


def test_SourceWidget_toggle_star(mocker):
    """
    The toggle_star method should call self.controller.update_star
    """
    mock_controller = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    event = mocker.MagicMock()

    sw = SourceWidget(None, mock_source)
    sw.controller = mock_controller
    sw.controller.update_star = mocker.MagicMock()

    sw.toggle_star(event)
    sw.controller.update_star.assert_called_once_with(mock_source)


def test_SourceWidget_delete_source(mocker, session, source):
    mock_delete_source_message_box_object = mocker.MagicMock(DeleteSourceMessageBox)
    mock_controller = mocker.MagicMock()
    mock_delete_source_message = mocker.MagicMock(
        return_value=mock_delete_source_message_box_object)

    sw = SourceWidget(None, source['source'])
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
    sw = SourceWidget(None, source)
    sw.controller = mock_controller

    mocker.patch(
        "securedrop_client.gui.widgets.QMessageBox.question",
        mock_message_box_question,
    )
    sw.delete_source(None)
    sw.controller.delete_source.assert_not_called()


def test_LoginDialog_setup(mocker):
    """
    The LoginView is correctly initialised.
    """
    mock_controller = mocker.MagicMock()
    ld = LoginDialog(None)
    ld.setup(mock_controller)
    assert ld.controller == mock_controller
    assert ld.title.text() == '<h1>Sign in</h1>'


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


def test_LoginDialog_error(mocker):
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
    source = factory.Source()
    file_ = factory.File(is_downloaded=True)

    fw = FileWidget(source, file_, mock_controller, mock_signal, align='left')

    assert isinstance(fw.layout.takeAt(0), QWidgetItem)
    assert isinstance(fw.layout.takeAt(0), QWidgetItem)
    assert isinstance(fw.layout.takeAt(0), QSpacerItem)
    assert fw.controller == mock_controller


def test_FileWidget_init_right(mocker):
    """
    Check the FileWidget is configured correctly for align-right.
    """
    mock_controller = mocker.MagicMock()
    mock_signal = mocker.MagicMock()  # not important for this test
    source = factory.Source()
    file_ = factory.File(is_downloaded=True)

    fw = FileWidget(source, file_, mock_controller, mock_signal, align='right')
    assert isinstance(fw.layout.takeAt(0), QSpacerItem)
    assert isinstance(fw.layout.takeAt(0), QWidgetItem)
    assert isinstance(fw.layout.takeAt(0), QWidgetItem)
    assert fw.controller == mock_controller


def test_FileWidget_mousePressEvent_download(mocker):
    """
    Should fire the expected download event handler in the logic layer.
    """
    mock_controller = mocker.MagicMock()
    mock_signal = mocker.MagicMock()  # not important for this test
    source = factory.Source()
    file_ = factory.File(is_downloaded=False)

    fw = FileWidget(source, file_, mock_controller, mock_signal)
    fw.mouseReleaseEvent(None)
    fw.controller.on_file_download.assert_called_once_with(source, file_)


def test_FileWidget_mousePressEvent_open(mocker):
    """
    Should fire the expected open event handler in the logic layer.
    """
    mock_controller = mocker.MagicMock()
    mock_signal = mocker.MagicMock()  # not important for this test
    source = factory.Source()
    file_ = factory.File(is_downloaded=True)

    fw = FileWidget(source, file_, mock_controller, mock_signal)
    fw.mouseReleaseEvent(None)
    fw.controller.on_file_open.assert_called_once_with(file_)


def test_FileWidget_clear_deletes_items(mocker, homedir):
    """
    Calling the clear() method on FileWidget should delete the existing items in the layout.
    """
    mock_controller = mocker.MagicMock()
    mock_signal = mocker.MagicMock()  # not important for this test
    source = factory.Source()
    file_ = factory.File(is_downloaded=True)

    fw = FileWidget(source, file_, mock_controller, mock_signal)
    assert fw.layout.count() != 0

    fw.clear()

    assert fw.layout.count() == 0


def test_FileWidget_on_file_download_updates_items_when_uuid_matches(mocker, homedir):
    """
    The _on_file_download method should clear and update the FileWidget
    """
    mock_controller = mocker.MagicMock()
    mock_signal = mocker.MagicMock()  # not important for this test
    source = factory.Source()
    file_ = factory.File(is_downloaded=True)

    fw = FileWidget(source, file_, mock_controller, mock_signal)
    fw.clear = mocker.MagicMock()
    fw.update = mocker.MagicMock()

    fw._on_file_download(file_.uuid)

    fw.clear.assert_called_once_with()
    fw.update.assert_called_once_with()


def test_FileWidget_on_file_download_updates_items_when_uuid_does_not_match(mocker, homedir):
    """
    The _on_file_download method should clear and update the FileWidget
    """
    mock_controller = mocker.MagicMock()
    mock_signal = mocker.MagicMock()  # not important for this test
    source = factory.Source()
    file_ = factory.File(is_downloaded=True)

    fw = FileWidget(source, file_, mock_controller, mock_signal)
    fw.clear = mocker.MagicMock()
    fw.update = mocker.MagicMock()

    fw._on_file_download('not a matching uuid')

    fw.clear.assert_not_called()
    fw.update.assert_not_called()


def test_ConversationView_init(mocker, homedir):
    """
    Ensure the conversation view has a layout to add widgets to.
    """
    mocked_source = mocker.MagicMock()
    mocked_controller = mocker.MagicMock()
    cv = ConversationView(mocked_source, homedir, mocked_controller)
    assert isinstance(cv.conversation_layout, QVBoxLayout)


def test_ConversationView_update_conversation_position_follow(mocker, homedir):
    """
    Check the signal handler sets the correct value for the scrollbar to be
    the maximum possible value, when the scrollbar is near the bottom, meaning
    it is following the conversation.
    """
    mocked_source = mocker.MagicMock()
    mocked_controller = mocker.MagicMock()

    cv = ConversationView(mocked_source, homedir, mocked_controller)

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

    cv = ConversationView(mocked_source, homedir, mocked_controller)

    cv.scroll.verticalScrollBar().value = mocker.MagicMock(return_value=5500)
    cv.scroll.viewport().height = mocker.MagicMock(return_value=500)
    cv.scroll.verticalScrollBar().setValue = mocker.MagicMock()

    cv.update_conversation_position(0, 6000)

    cv.scroll.verticalScrollBar().setValue.assert_not_called()


def test_ConversationView_add_message(mocker, homedir, session, source):
    """
    Adding a message results in a new MessageWidget added to the layout.
    """
    source = source['source']  # grab the source from the fixture dict for simplicity

    mock_message_ready_signal = mocker.MagicMock()
    mock_message_sync = mocker.MagicMock(message_ready=mock_message_ready_signal)
    mocked_controller = mocker.MagicMock(session=session,
                                         message_sync=mock_message_sync)

    content = 'a sea, a bee'
    message = factory.Message(source=source, content=content)
    session.add(message)
    session.commit()

    cv = ConversationView(source, homedir, mocked_controller)
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


def test_ConversationView_add_message_no_content(mocker, homedir, session, source):
    """
    Adding a message results in a new MessageWidget added to the layout. This case specifically
    checks that if a `Message` has `content = None` that a helpful message is displayed as would
    be the case if download/decryption never occurred or failed.
    """
    source = source['source']  # grab the source from the fixture dict for simplicity

    mock_message_ready_signal = mocker.MagicMock()
    mock_message_sync = mocker.MagicMock(message_ready=mock_message_ready_signal)
    mocked_controller = mocker.MagicMock(session=session,
                                         message_sync=mock_message_sync)

    message = factory.Message(source=source, is_decrypted=False, content=None)
    session.add(message)
    session.commit()

    cv = ConversationView(source, homedir, mocked_controller)
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


def test_ConversationView_add_reply(mocker, homedir, session, source):
    """
    Adding a message results in a new ReplyWidget added to the layout.
    """
    source = source['source']  # grab the source from the fixture dict for simplicity

    mock_reply_ready_signal = mocker.MagicMock()
    mock_reply_succeeded_signal = mocker.MagicMock()
    mock_reply_failed_signal = mocker.MagicMock()
    mock_reply_sync = mocker.MagicMock(reply_ready=mock_reply_ready_signal)
    mocked_controller = mocker.MagicMock(session=session,
                                         reply_sync=mock_reply_sync,
                                         reply_succeeded=mock_reply_succeeded_signal,
                                         reply_failed=mock_reply_failed_signal)

    content = 'a sea, a bee'
    reply = factory.Reply(source=source, content=content)
    session.add(reply)
    session.commit()

    cv = ConversationView(source, homedir, mocked_controller)
    cv.conversation_layout = mocker.MagicMock()
    # this is the Reply that __init__() would return
    mock_reply_widget_res = mocker.MagicMock()
    # mock the actual MessageWidget so we can inspect the __init__ call
    mock_reply_widget = mocker.patch('securedrop_client.gui.widgets.ReplyWidget',
                                     return_value=mock_reply_widget_res)

    cv.add_reply(reply.uuid, content)

    # check that we built the widget was called with the correct args
    mock_reply_widget.assert_called_once_with(
        reply.uuid,
        content,
        mock_reply_ready_signal,
        mock_reply_succeeded_signal,
        mock_reply_failed_signal)

    # check that we added the correct widget to the layout
    cv.conversation_layout.addWidget.assert_called_once_with(mock_reply_widget_res)


def test_ConversationView_add_reply_no_content(mocker, homedir, session, source):
    """
    Adding a reply results in a new ReplyWidget added to the layout. This case specifically
    checks that if a `Reply` has `content = None` that a helpful message is displayed as would
    be the case if download/decryption never occurred or failed.
    """
    source = source['source']  # grab the source from the fixture dict for simplicity

    mock_reply_ready_signal = mocker.MagicMock()
    mock_reply_succeeded_signal = mocker.MagicMock()
    mock_reply_failed_signal = mocker.MagicMock()
    mock_reply_sync = mocker.MagicMock(reply_ready=mock_reply_ready_signal)
    mocked_controller = mocker.MagicMock(session=session,
                                         reply_sync=mock_reply_sync,
                                         reply_succeeded=mock_reply_succeeded_signal,
                                         reply_failed=mock_reply_failed_signal)

    reply = factory.Reply(source=source, is_decrypted=False, content=None)
    session.add(reply)
    session.commit()

    cv = ConversationView(source, homedir, mocked_controller)
    cv.conversation_layout = mocker.MagicMock()
    # this is the Reply that __init__() would return
    mock_reply_widget_res = mocker.MagicMock()
    # mock the actual MessageWidget so we can inspect the __init__ call
    mock_reply_widget = mocker.patch('securedrop_client.gui.widgets.ReplyWidget',
                                     return_value=mock_reply_widget_res)

    cv.add_reply(reply.uuid, '<Reply not yet available>')

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

    cv = ConversationView(mocked_source, homedir, mocked_controller)
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


def test_ConversationView_add_not_downloaded_file(mocker, homedir):
    """
    Adding a file results in a new FileWidget added to the layout with the
    proper QLabel.
    """
    mocked_source = mocker.MagicMock()
    mocked_controller = mocker.MagicMock()

    cv = ConversationView(mocked_source, homedir, mocked_controller)
    cv.conversation_layout = mocker.MagicMock()

    mock_source = mocker.MagicMock()
    mock_file = mocker.MagicMock()
    mock_file.is_downloaded = False
    mock_file.size = 123
    mock_label = mocker.patch('securedrop_client.gui.widgets.QLabel')
    mocker.patch('securedrop_client.gui.widgets.QHBoxLayout.addWidget')
    mocker.patch('securedrop_client.gui.widgets.FileWidget.setLayout')

    cv.add_file(mock_source, mock_file)
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
        source_widget = SourceWidget(None, mock_source)
        source_widget.setup(mock_controller)
        source_widget.delete_source(mock_event)
        mock_delete_source_message_box_obj.launch.assert_not_called()


def test_SourceConversationWrapper_send_reply(mocker):
    mock_source = mocker.Mock()
    mock_source.uuid = 'abc123'
    mock_source.collection = []
    mock_uuid = '456xyz'
    mocker.patch('securedrop_client.gui.widgets.uuid4', return_value=mock_uuid)
    mock_controller = mocker.MagicMock()
    mocker.patch('securedrop_client.gui.widgets.LastUpdatedLabel', return_value=QLabel('now'))

    cw = SourceConversationWrapper(mock_source, 'mock home', mock_controller, True)
    mock_add_reply = mocker.Mock()
    cw.conversation.add_reply = mock_add_reply

    msg = 'Alles für Alle'
    cw.send_reply(msg)

    mock_add_reply.assert_called_once_with(mock_uuid, msg)
    mock_controller.send_reply.assert_called_once_with(mock_source.uuid, mock_uuid, msg)


def test_ReplyBoxWidget_send_reply(mocker):
    mock_conversation = mocker.Mock()
    rw = ReplyBoxWidget(mock_conversation)

    # when empty, don't sent message
    assert not rw.text_edit.toPlainText()  # precondition
    rw.send_reply()
    assert not mock_conversation.send_reply.called

    # when only whitespace, don't sent message
    rw.text_edit.setText('  \n\n  ')
    rw.send_reply()
    assert not mock_conversation.send_reply.called

    # send send send send
    msg = 'nein'
    rw.text_edit.setText(msg)
    rw.send_reply()
    mock_conversation.send_reply.assert_called_once_with(msg)


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


def test_update_conversation_maintains_old_items(mocker, homedir, session):
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

    cv = ConversationView(source, homedir, mock_controller)
    assert cv.conversation_layout.count() == 3

    cv.update_conversation(cv.source.collection)

    assert cv.conversation_layout.count() == 3


def test_update_conversation_adds_new_items(mocker, homedir, session):
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

    cv = ConversationView(source, homedir, mock_controller)
    assert cv.conversation_layout.count() == 3  # precondition

    # add the new message and persist
    new_message = factory.Message(filename='4-source-msg.gpg', source=source)
    session.add(new_message)
    session.commit()

    cv.update_conversation(cv.source.collection)
    assert cv.conversation_layout.count() == 4


def test_clear_conversation_deletes_items(mocker, homedir):
    """
    Calling clear_conversation deletes items from layout
    """
    mock_controller = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    message = db.Message(uuid='uuid', content='message', filename='1-foo')
    cv = ConversationView(mock_source, homedir, mock_controller)
    cv.add_message(message)
    assert cv.conversation_layout.count() == 1

    cv.clear_conversation()

    assert cv.conversation_layout.count() == 0


def test_SourceConversationWrapper_auth_signals(mocker, homedir):
    """
    Ensure we connect to the auth signal and set the intial state on update
    """
    mock_source = mocker.Mock(collection=[])
    mock_connect = mocker.MagicMock()
    mock_signal = mocker.MagicMock(connect=mock_connect)
    mock_controller = mocker.MagicMock(authentication_state=mock_signal)
    mock_is_auth = mocker.MagicMock()

    mock_sh = mocker.patch.object(SourceConversationWrapper, '_show_or_hide_replybox')
    mocker.patch('securedrop_client.gui.widgets.LastUpdatedLabel', return_value=QLabel('now'))

    SourceConversationWrapper(mock_source, 'mock home', mock_controller, mock_is_auth)

    mock_connect.assert_called_once_with(mock_sh)
    mock_sh.assert_called_with(mock_is_auth)


def test_SourceConversationWrapper_set_widgets_via_auth_value(mocker, homedir):
    """
    When the client is authenticated, we should create a ReplyBoxWidget otherwise a warning.
    """
    mock_source = mocker.Mock(collection=[])
    mock_controller = mocker.MagicMock()

    mocker.patch('securedrop_client.gui.widgets.LastUpdatedLabel', return_value=QLabel('now'))
    cw = SourceConversationWrapper(mock_source, 'mock home', mock_controller, True)
    mocker.patch.object(cw, 'layout')
    mock_reply_box = mocker.patch('securedrop_client.gui.widgets.ReplyBoxWidget',
                                  return_value=QWidget())
    mock_label = mocker.patch('securedrop_client.gui.widgets.QLabel', return_value=QWidget())

    cw._show_or_hide_replybox(True)
    mock_reply_box.assert_called_once_with(cw)
    assert not mock_label.called

    mock_reply_box.reset_mock()

    cw._show_or_hide_replybox(False)
    assert not mock_reply_box.called
    assert mock_label.called
