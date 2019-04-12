"""
Check the core Window UI class works as expected.
"""
from PyQt5.QtWidgets import QApplication, QHBoxLayout
from securedrop_client.db import Message
from securedrop_client.gui.main import Window
from securedrop_client.resources import load_icon
from uuid import uuid4

app = QApplication([])


def test_init(mocker):
    """
    Ensure the Window instance is setup in the expected manner.
    """
    mock_li = mocker.MagicMock(return_value=load_icon('icon.png'))
    mock_lo = mocker.MagicMock(return_value=QHBoxLayout())
    mock_lo().addWidget = mocker.MagicMock()

    mocker.patch('securedrop_client.gui.main.load_icon', mock_li)
    mock_lp = mocker.patch('securedrop_client.gui.main.LeftPane')
    mock_mv = mocker.patch('securedrop_client.gui.main.MainView')
    mocker.patch('securedrop_client.gui.main.QHBoxLayout', mock_lo)
    mocker.patch('securedrop_client.gui.main.QMainWindow')

    w = Window('mock')
    mock_li.assert_called_once_with(w.icon)
    mock_lp.assert_called_once_with()
    mock_mv.assert_called_once_with(w.widget)
    assert mock_lo().addWidget.call_count == 2


def test_setup(mocker):
    """
    Ensure the passed in controller is referenced and the various views are
    instantiated as expected.
    """
    w = Window('mock')
    mock_controller = mocker.MagicMock()
    w.setup(mock_controller)
    assert w.controller == mock_controller


def test_autosize_window(mocker):
    """
    Check the autosizing fits to the full screen size.
    """
    w = Window('mock')
    w.resize = mocker.MagicMock()
    mock_screen = mocker.MagicMock()
    mock_screen.width.return_value = 1024
    mock_screen.height.return_value = 768
    mock_sg = mocker.MagicMock()
    mock_sg.screenGeometry.return_value = mock_screen
    mock_qdw = mocker.MagicMock(return_value=mock_sg)
    mocker.patch('securedrop_client.gui.main.QDesktopWidget', mock_qdw)
    w.autosize_window()
    w.resize.assert_called_once_with(1024, 768)


def test_show_login(mocker):
    """
    The login dialog is displayed with a clean state.
    """
    mock_controller = mocker.MagicMock()
    w = Window('mock')
    w.setup(mock_controller)
    mock_ld = mocker.patch('securedrop_client.gui.main.LoginDialog')

    w.show_login()

    mock_ld.assert_called_once_with(w)
    w.login_dialog.reset.assert_called_once_with()
    w.login_dialog.exec.assert_called_once_with()


def test_show_login_error(mocker):
    """
    Ensures that an error message is displayed in the login dialog.
    """
    mock_controller = mocker.MagicMock()
    w = Window('mock')
    w.setup(mock_controller)
    w.login_dialog = mocker.MagicMock()
    w.show_login_error('boom')
    w.login_dialog.error.assert_called_once_with('boom')


def test_hide_login(mocker):
    """
    Ensure the login dialog is closed and hidden.
    """
    mock_controller = mocker.MagicMock()
    w = Window('mock')
    w.setup(mock_controller)
    ld = mocker.MagicMock()
    w.login_dialog = ld
    w.hide_login()
    ld.accept.assert_called_once_with()
    assert w.login_dialog is None


def test_show_sources(mocker):
    """
    Ensure the sources list is passed to the source list widget to be updated.
    """
    w = Window('mock')
    w.main_view = mocker.MagicMock()
    w.show_sources([1, 2, 3])
    w.main_view.source_list.update.assert_called_once_with([1, 2, 3])


def test_update_error_status_default(mocker):
    """
    Ensure that the error to be shown in the error status bar will be passed to the top pane with a
    default duration of 10 seconds.
    """
    w = Window('mock')
    w.top_pane = mocker.MagicMock()
    w.update_error_status(message='test error message')
    w.top_pane.update_error_status.assert_called_once_with('test error message', 10000)


def test_update_error_status(mocker):
    """
    Ensure that the error to be shown in the error status bar will be passed to the top pane with
    the duration of seconds provided.
    """
    w = Window('mock')
    w.top_pane = mocker.MagicMock()
    w.update_error_status(message='test error message', duration=123)
    w.top_pane.update_error_status.assert_called_once_with('test error message', 123)


def test_update_activity_status_default(mocker):
    """
    Ensure that the activity to be shown in the activity status bar will be passed to the top pane
    with a default duration of 0 seconds, i.e. forever.
    """
    w = Window('mock')
    w.top_pane = mocker.MagicMock()
    w.update_activity_status(message='test message')
    w.top_pane.update_activity_status.assert_called_once_with('test message', 0)


def test_update_activity_status(mocker):
    """
    Ensure that the activity to be shown in the activity status bar will be passed to the top pane
    with the duration of seconds provided.
    """
    w = Window('mock')
    w.top_pane = mocker.MagicMock()
    w.update_activity_status(message='test message', duration=123)
    w.top_pane.update_activity_status.assert_called_once_with('test message', 123)


def test_clear_error_status(mocker):
    """
    Ensure clear_error_status is called.
    """
    w = Window('mock')
    w.top_pane = mocker.MagicMock()

    w.clear_error_status()

    w.top_pane.clear_error_status.assert_called_once_with()


def test_show_sync(mocker):
    """
    If there's a value display the result of its "humanize" method.humanize
    """
    w = Window('mock')
    w.update_activity_status = mocker.MagicMock()
    updated_on = mocker.MagicMock()
    w.show_sync(updated_on)
    w.update_activity_status.assert_called_once_with(
        'Last refresh: {}'.format(updated_on.humanize()))


def test_show_sync_no_sync(mocker):
    """
    If there's no value to display, default to a "waiting" message.
    """
    w = Window('mock')
    w.update_activity_status = mocker.MagicMock()
    w.show_sync(None)
    w.update_activity_status.assert_called_once_with('Waiting to refresh...', 5000)


def test_set_logged_in_as(mocker):
    """
    Given a username, the left pane is appropriately called to update.
    """
    w = Window('mock')
    w.left_pane = mocker.MagicMock()
    w.set_logged_in_as('test')
    w.left_pane.set_logged_in_as.assert_called_once_with('test')


def test_logout(mocker):
    """
    Ensure the left pane updates to the logged out state.
    """
    w = Window('mock')
    w.left_pane = mocker.MagicMock()
    w.top_pane = mocker.MagicMock()

    w.logout()

    w.left_pane.set_logged_out.assert_called_once_with()
    w.top_pane.disable_refresh.assert_called_once_with()


def test_on_source_changed(mocker):
    """
    Ensure the event handler for when a source is changed calls the
    show_conversation_for method with the expected source object.
    """
    w = Window('mock')
    w.main_view = mocker.MagicMock()
    w.main_view.source_list.currentItem()
    mock_sw = w.main_view.source_list.itemWidget()
    w.show_conversation_for = mocker.MagicMock()
    mock_controller = mocker.MagicMock(is_authenticated=True)
    w.controller = mock_controller
    w.on_source_changed()
    w.show_conversation_for.assert_called_once_with(mock_sw.source,
                                                    mock_controller.is_authenticated)


def test_conversation_for(mocker):
    """
    Test that the source collection is displayed in the conversation view.
    """
    w = Window('mock')
    w.controller = mocker.MagicMock()
    w.main_view = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    mock_source.journalistic_designation = 'Testy McTestface'
    mock_file = mocker.MagicMock()
    mock_file.filename = '1-my-source-doc.gpg'
    mock_message = mocker.MagicMock()
    mock_message.filename = '2-my-source-msg.gpg'
    mock_reply = mocker.MagicMock()
    mock_reply.filename = '3-my-source-reply.gpg'
    mock_source.collection = [mock_file, mock_message, mock_reply]

    mocked_add_message = mocker.patch('securedrop_client.gui.widgets.ConversationView.add_message',
                                      new=mocker.Mock())
    mocked_add_reply = mocker.patch('securedrop_client.gui.widgets.ConversationView.add_reply',
                                    new=mocker.Mock())
    mocked_add_file = mocker.patch('securedrop_client.gui.widgets.ConversationView.add_file',
                                   new=mocker.Mock())

    w.show_conversation_for(mock_source, is_authenticated=True)

    assert mocked_add_message.call_count > 0
    assert mocked_add_reply.call_count > 0
    assert mocked_add_file.call_count > 0

    # check that showing the conversation a second time doesn't break anything

    # stop the old mockers
    mocked_add_message.stop()
    mocked_add_reply.stop()
    mocked_add_file.stop()

    # use new mocks to check the count again
    mocked_add_message = mocker.patch('securedrop_client.gui.widgets.ConversationView.add_message',
                                      new=mocker.Mock())
    mocked_add_reply = mocker.patch('securedrop_client.gui.widgets.ConversationView.add_reply',
                                    new=mocker.Mock())
    mocked_add_file = mocker.patch('securedrop_client.gui.widgets.ConversationView.add_file',
                                   new=mocker.Mock())

    # checking with is_authenticated=False just to ensure this doesn't break either
    w.show_conversation_for(mock_source, is_authenticated=False)

    # because the conversation was cached, we don't call these functions again
    assert mocked_add_message.call_count == 0
    assert mocked_add_reply.call_count == 0
    assert mocked_add_file.call_count == 0


def test_conversation_pending_message(mocker):
    """
    Test that a conversation with a message that's not yet downloaded
    shows the right placeholder text
    """
    w = Window('mock')
    w.controller = mocker.MagicMock()
    w.main_view = mocker.MagicMock()
    w._add_item_content_or = mocker.MagicMock()
    mock_source = mocker.MagicMock()
    mock_source.journalistic_designation = 'Testy McTestface'

    msg_uuid = str(uuid4())
    message = Message(source=mock_source, uuid=msg_uuid, size=123, filename="1-test.msg.gpg",
                      download_url='http://test/test', is_downloaded=False)

    mock_source.collection = [message]

    mocked_add_message = mocker.patch('securedrop_client.gui.widgets.ConversationView.add_message')
    mocker.patch('securedrop_client.gui.main.QHBoxLayout')
    mocker.patch('securedrop_client.gui.main.QWidget')

    w.show_conversation_for(mock_source, True)

    assert mocked_add_message.call_count == 1
    assert mocked_add_message.call_args == mocker.call(message)
