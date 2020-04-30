"""
Check the core Window UI class works as expected.
"""
from PyQt5.QtWidgets import QApplication, QHBoxLayout

from securedrop_client.gui.main import Window
from securedrop_client.resources import load_icon


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

    w = Window()

    mock_li.assert_called_once_with(w.icon)
    mock_lp.assert_called_once_with()
    mock_mv.assert_called_once_with(w.main_pane)
    assert mock_lo().addWidget.call_count == 2


def test_setup(mocker):
    """
    Ensure the passed in controller is referenced and the various views are
    instantiated as expected.
    """
    mock_controller = mocker.MagicMock()

    w = Window()
    w.show_login = mocker.MagicMock()
    w.top_pane = mocker.MagicMock()
    w.left_pane = mocker.MagicMock()
    w.main_view = mocker.MagicMock()

    w.setup(mock_controller)

    assert w.controller == mock_controller
    w.top_pane.setup.assert_called_once_with(mock_controller)
    w.left_pane.setup.assert_called_once_with(w, mock_controller)
    w.main_view.setup.assert_called_once_with(mock_controller)
    w.show_login.assert_called_once_with()


def test_show_main_window(mocker):
    w = Window()
    w.autosize_window = mocker.MagicMock()
    w.show = mocker.MagicMock()
    w.set_logged_in_as = mocker.MagicMock()
    user = mocker.MagicMock()

    w.show_main_window(db_user=user)

    w.autosize_window.assert_called_once_with()
    w.show.assert_called_once_with()
    w.set_logged_in_as.assert_called_once_with(user)


def test_show_main_window_without_username(mocker):
    w = Window()
    w.autosize_window = mocker.MagicMock()
    w.show = mocker.MagicMock()
    w.set_logged_in_as = mocker.MagicMock()

    w.show_main_window()

    w.autosize_window.assert_called_once_with()
    w.show.assert_called_once_with()
    w.set_logged_in_as.called is False


def test_autosize_window(mocker):
    """
    Check the autosizing fits to the full screen size.
    """
    w = Window()
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
    w = Window()
    w.controller = mocker.MagicMock()
    mock_ld = mocker.patch('securedrop_client.gui.main.LoginDialog')

    w.show_login()

    mock_ld.assert_called_once_with(w)
    w.login_dialog.reset.assert_called_once_with()
    w.login_dialog.show.assert_called_once_with()


def test_show_login_with_error_message(mocker):
    """
    The login dialog is displayed with a clean state.
    """
    w = Window()
    w.controller = mocker.MagicMock()
    mock_ld = mocker.patch('securedrop_client.gui.main.LoginDialog')

    w.show_login('this-is-an-error-message-to-show-on-login-window')

    mock_ld.assert_called_once_with(w)
    w.login_dialog.reset.assert_called_once_with()
    w.login_dialog.show.assert_called_once_with()
    w.login_dialog.error.assert_called_once_with('this-is-an-error-message-to-show-on-login-window')


def test_show_login_error(mocker):
    """
    Ensures that an error message is displayed in the login dialog.
    """
    w = Window()
    w.show_login = mocker.MagicMock()
    w.setup(mocker.MagicMock())
    w.login_dialog = mocker.MagicMock()

    w.show_login_error('boom')

    w.login_dialog.error.assert_called_once_with('boom')


def test_hide_login(mocker):
    """
    Ensure the login dialog is closed and hidden.
    """
    w = Window()
    w.show_login = mocker.MagicMock()
    ld = mocker.MagicMock()
    w.login_dialog = ld

    w.hide_login()

    ld.accept.assert_called_once_with()
    assert w.login_dialog is None


def test_refresh_current_source_conversation(mocker):
    """
    Ensure on_source_changed is called on the MainView (which
    updates the current conversation) when
    refresh_current_source_conversation() is called.
    """
    w = Window()
    w.main_view = mocker.MagicMock()

    w.refresh_current_source_conversation()

    w.main_view.on_source_changed.assert_called_once_with()


def test_show_sources(mocker):
    """
    Ensure the sources list is passed to the main view to be updated.
    """
    w = Window()
    w.main_view = mocker.MagicMock()
    w.show_sources([1, 2, 3])
    w.main_view.show_sources.assert_called_once_with([1, 2, 3])


def test_update_error_status_default(mocker):
    """
    Ensure that the error to be shown in the error status bar will be passed to the top pane with a
    default duration of 10 seconds.
    """
    w = Window()
    w.top_pane = mocker.MagicMock()
    w.update_error_status(message='test error message')
    w.top_pane.update_error_status.assert_called_once_with('test error message', 10000)


def test_update_error_status(mocker):
    """
    Ensure that the error to be shown in the error status bar will be passed to the top pane with
    the duration of seconds provided.
    """
    w = Window()
    w.top_pane = mocker.MagicMock()
    w.update_error_status(message='test error message', duration=123)
    w.top_pane.update_error_status.assert_called_once_with('test error message', 123)


def test_update_activity_status_default(mocker):
    """
    Ensure that the activity to be shown in the activity status bar will be passed to the top pane
    with a default duration of 0 seconds, i.e. forever.
    """
    w = Window()
    w.top_pane = mocker.MagicMock()
    w.update_activity_status(message='test message')
    w.top_pane.update_activity_status.assert_called_once_with('test message', 0)


def test_update_activity_status(mocker):
    """
    Ensure that the activity to be shown in the activity status bar will be passed to the top pane
    with the duration of seconds provided.
    """
    w = Window()
    w.top_pane = mocker.MagicMock()
    w.update_activity_status(message='test message', duration=123)
    w.top_pane.update_activity_status.assert_called_once_with('test message', 123)


def test_clear_error_status(mocker):
    """
    Ensure clear_error_status is called.
    """
    w = Window()
    w.top_pane = mocker.MagicMock()

    w.clear_error_status()

    w.top_pane.clear_error_status.assert_called_once_with()


def test_show_last_sync(mocker):
    """
    If there's a value display the result of its "humanize" method.humanize
    """
    w = Window()
    w.update_activity_status = mocker.MagicMock()
    updated_on = mocker.MagicMock()
    w.show_last_sync(updated_on)
    w.update_activity_status.assert_called_once_with(
        'Last Refresh: {}'.format(updated_on.humanize()))


def test_show_last_sync_no_sync(mocker):
    """
    If there's no value to display, default to a "waiting" message.
    """
    w = Window()
    w.update_activity_status = mocker.MagicMock()
    w.show_last_sync(None)
    w.update_activity_status.assert_called_once_with('Last Refresh: never')


def test_set_logged_in_as(mocker):
    """
    Given a username, the left pane is appropriately called to update.
    """
    w = Window()
    w.left_pane = mocker.MagicMock()

    w.set_logged_in_as('test')

    w.left_pane.set_logged_in_as.assert_called_once_with('test')


def test_logout(mocker):
    """
    Ensure the left pane updates to the logged out state.
    """
    w = Window()
    w.left_pane = mocker.MagicMock()
    w.top_pane = mocker.MagicMock()

    w.logout()

    w.left_pane.set_logged_out.assert_called_once_with()
    w.top_pane.set_logged_out.assert_called_once_with()


def test_clear_clipboard(mocker):
    """
    Ensure we are clearing the system-level clipboard in the expected manner.
    """
    mock_clipboard = mocker.MagicMock()
    mocker.patch('securedrop_client.gui.main.QApplication.clipboard',
                 return_value=mock_clipboard)
    w = Window()
    w.clear_clipboard()
    mock_clipboard.clear.assert_called_once_with()
