"""
Check the core Window UI class works as expected.
"""
import unittest

from PyQt5.QtWidgets import QApplication, QHBoxLayout

from securedrop_client.gui.main import Window
from securedrop_client.logic import Controller
from securedrop_client.resources import load_icon

app = QApplication([])


class WindowTest(unittest.TestCase):
    def setUp(self):
        self._clipboard = QApplication.clipboard()
        self.window = Window(self._clipboard)

    def test_clear_clipboard(self):
        self._clipboard.setText("The clipboard is not empty")

        self.window.clear_clipboard()
        assert self._clipboard.text() == ""


def test_init(mocker):
    """
    Ensure the Window instance is setup in the expected manner.
    """
    mock_li = mocker.MagicMock(return_value=load_icon("icon.png"))
    mock_lo = mocker.MagicMock(return_value=QHBoxLayout())
    mock_lo().addWidget = mocker.MagicMock()
    mocker.patch("securedrop_client.gui.main.load_icon", mock_li)
    mock_lp = mocker.patch("securedrop_client.gui.main.LeftPane")
    mock_mv = mocker.patch("securedrop_client.gui.main.MainView")
    mocker.patch("securedrop_client.gui.main.QHBoxLayout", mock_lo)
    mocker.patch("securedrop_client.gui.main.QMainWindow")
    mocker.patch("securedrop_client.gui.main.Window.setStyleSheet")
    load_css = mocker.patch("securedrop_client.gui.main.load_css")

    w = Window(QApplication.clipboard())

    mock_li.assert_called_once_with(w.icon)
    mock_lp.assert_called_once_with()
    mock_mv.assert_called_once_with(w.main_pane)
    assert mock_lo().addWidget.call_count == 2
    load_css.assert_called_once_with("sdclient.css")


def test_setup(mocker, homedir, session_maker):
    """
    Ensure the passed in controller is referenced and the various views are
    instantiated as expected.
    """
    w = Window(QApplication.clipboard())
    w.show_login = mocker.MagicMock()
    w.top_pane = mocker.MagicMock()
    w.left_pane = mocker.MagicMock()
    w.main_view = mocker.MagicMock()
    controller = Controller("http://localhost", mocker.MagicMock(), session_maker, homedir)

    w.setup(controller)

    assert w.controller == controller
    w.top_pane.setup.assert_called_once_with(controller)
    w.left_pane.setup.assert_called_once_with(w, controller)
    w.main_view.setup.assert_called_once_with(controller)
    w.show_login.assert_called_once_with()


def test_show_main_window(mocker, homedir, session_maker):
    w = Window(QApplication.clipboard())
    controller = Controller("http://localhost", w, session_maker, homedir)
    w.setup(controller)
    w.show = mocker.MagicMock()
    w.showMaximized = mocker.MagicMock()
    w.set_logged_in_as = mocker.MagicMock()
    user = mocker.MagicMock()

    w.show_main_window(db_user=user)

    w.show.assert_called_once_with()
    w.showMaximized.assert_not_called()
    w.set_logged_in_as.assert_called_once_with(user)

    controller.qubes = False
    w.setup(controller)
    w.show.reset_mock()
    w.showMaximized.reset_mock()
    w.set_logged_in_as.reset_mock()

    w.show_main_window(db_user=user)

    w.show.assert_not_called()
    w.showMaximized.assert_called_once_with()
    w.set_logged_in_as.assert_called_once_with(user)


def test_show_main_window_when_already_showing(mocker, homedir, session_maker):
    """
    Ensure we don't maximize the main window if it's already showing.
    """
    w = Window(QApplication.clipboard())
    controller = Controller("http://localhost", w, session_maker, homedir)
    w.setup(controller)
    w.show = mocker.MagicMock()
    w.showMaximized = mocker.MagicMock()
    w.set_logged_in_as = mocker.MagicMock()
    user = mocker.MagicMock()
    w.isHidden = mocker.MagicMock(return_value=False)

    w.show_main_window(db_user=user)

    w.show.assert_not_called()
    w.showMaximized.assert_not_called()
    w.set_logged_in_as.assert_called_once_with(user)

    controller.qubes = False
    w.setup(controller)
    w.show.reset_mock()
    w.showMaximized.reset_mock()
    w.set_logged_in_as.reset_mock()

    w.show_main_window(db_user=user)

    w.show.assert_not_called()
    w.showMaximized.assert_not_called()
    w.set_logged_in_as.assert_called_once_with(user)


def test_show_main_window_without_username(mocker, homedir, session_maker):
    w = Window(QApplication.clipboard())
    controller = Controller("http://localhost", w, session_maker, homedir)
    w.setup(controller)
    w.show = mocker.MagicMock()
    w.showMaximized = mocker.MagicMock()
    w.set_logged_in_as = mocker.MagicMock()

    w.show_main_window()

    w.show.assert_called_once_with()
    w.showMaximized.assert_not_called()
    w.set_logged_in_as.called is False

    controller.qubes = False
    w.setup(controller)
    w.show.reset_mock()
    w.showMaximized.reset_mock()
    w.set_logged_in_as.reset_mock()

    w.show_main_window()

    w.show.assert_not_called()
    w.showMaximized.assert_called_once_with()
    w.set_logged_in_as.called is False


def test_show_main_window_without_username_when_already_showing(mocker, homedir, session_maker):
    w = Window(QApplication.clipboard())
    controller = Controller("http://localhost", w, session_maker, homedir)
    w.setup(controller)
    w.show = mocker.MagicMock()
    w.showMaximized = mocker.MagicMock()
    w.set_logged_in_as = mocker.MagicMock()
    w.isHidden = mocker.MagicMock(return_value=False)

    w.show_main_window()

    w.show.assert_not_called()
    w.showMaximized.assert_not_called()
    w.set_logged_in_as.called is False

    controller.qubes = False
    w.setup(controller)
    w.show.reset_mock()
    w.showMaximized.reset_mock()
    w.set_logged_in_as.reset_mock()

    w.show_main_window()

    w.show.assert_not_called()
    w.showMaximized.assert_not_called()
    w.set_logged_in_as.called is False


def test_show_login(mocker):
    """
    The login dialog is displayed with a clean state.
    """
    w = Window(QApplication.clipboard())
    w.controller = mocker.MagicMock()
    mock_ld = mocker.patch("securedrop_client.gui.main.LoginDialog")

    w.show_login()

    mock_ld.assert_called_once_with(w)
    w.login_dialog.reset.assert_called_once_with()
    w.login_dialog.show.assert_called_once_with()


def test_show_login_with_error_message(mocker):
    """
    The login dialog is displayed with a clean state.
    """
    w = Window(QApplication.clipboard())
    w.controller = mocker.MagicMock()
    mock_ld = mocker.patch("securedrop_client.gui.main.LoginDialog")

    w.show_login("this-is-an-error-message-to-show-on-login-window")

    mock_ld.assert_called_once_with(w)
    w.login_dialog.reset.assert_called_once_with()
    w.login_dialog.show.assert_called_once_with()
    w.login_dialog.error.assert_called_once_with("this-is-an-error-message-to-show-on-login-window")


def test_show_login_error(mocker):
    """
    Ensures that an error message is displayed in the login dialog.
    """
    w = Window(QApplication.clipboard())
    w.show_login = mocker.MagicMock()
    w.setup(mocker.MagicMock())
    w.login_dialog = mocker.MagicMock()

    w.show_login_error("boom")

    w.login_dialog.error.assert_called_once_with("boom")


def test_hide_login(mocker):
    """
    Ensure the login dialog is closed and hidden.
    """
    w = Window(QApplication.clipboard())
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
    w = Window(QApplication.clipboard())
    w.main_view = mocker.MagicMock()

    w.refresh_current_source_conversation()

    w.main_view.refresh_source_conversations.assert_called_once_with()


def test_show_sources(mocker):
    """
    Ensure the sources list is passed to the main view to be updated.
    """
    w = Window(QApplication.clipboard())
    w.main_view = mocker.MagicMock()
    w.show_sources([1, 2, 3])
    w.main_view.show_sources.assert_called_once_with([1, 2, 3])


def test_update_error_status_default(mocker):
    """
    Ensure that the error to be shown in the error status bar will be passed to the top pane with a
    default duration of 10 seconds.
    """
    w = Window(QApplication.clipboard())
    w.top_pane = mocker.MagicMock()
    w.update_error_status(message="test error message")
    w.top_pane.update_error_status.assert_called_once_with("test error message", 10000)


def test_update_error_status(mocker):
    """
    Ensure that the error to be shown in the error status bar will be passed to the top pane with
    the duration of seconds provided.
    """
    w = Window(QApplication.clipboard())
    w.top_pane = mocker.MagicMock()
    w.update_error_status(message="test error message", duration=123)
    w.top_pane.update_error_status.assert_called_once_with("test error message", 123)


def test_update_activity_status_default(mocker):
    """
    Ensure that the activity to be shown in the activity status bar will be passed to the top pane
    with a default duration of 0 seconds, i.e. forever.
    """
    w = Window(QApplication.clipboard())
    w.top_pane = mocker.MagicMock()
    w.update_activity_status(message="test message")
    w.top_pane.update_activity_status.assert_called_once_with("test message", 0)


def test_update_activity_status(mocker):
    """
    Ensure that the activity to be shown in the activity status bar will be passed to the top pane
    with the duration of seconds provided.
    """
    w = Window(QApplication.clipboard())
    w.top_pane = mocker.MagicMock()
    w.update_activity_status(message="test message", duration=123)
    w.top_pane.update_activity_status.assert_called_once_with("test message", 123)


def test_clear_error_status(mocker):
    """
    Ensure clear_error_status is called.
    """
    w = Window(QApplication.clipboard())
    w.top_pane = mocker.MagicMock()

    w.clear_error_status()

    w.top_pane.clear_error_status.assert_called_once_with()


def test_show_last_sync(mocker):
    """
    If there's a value display the result of its "humanize" method.humanize
    """
    w = Window(QApplication.clipboard())
    w.update_activity_status = mocker.MagicMock()
    updated_on = mocker.MagicMock()
    w.show_last_sync(updated_on)
    w.update_activity_status.assert_called_once_with(
        "Last Refresh: {}".format(updated_on.humanize())
    )


def test_show_last_sync_no_sync(mocker):
    """
    If there's no value to display, default to a "waiting" message.
    """
    w = Window(QApplication.clipboard())
    w.update_activity_status = mocker.MagicMock()
    w.show_last_sync(None)
    w.update_activity_status.assert_called_once_with("Last Refresh: never")


def test_set_logged_in_as(mocker):
    """
    Given a username, the left pane is appropriately called to update.
    """
    w = Window(QApplication.clipboard())
    w.left_pane = mocker.MagicMock()

    w.set_logged_in_as("test")

    w.left_pane.set_logged_in_as.assert_called_once_with("test")


def test_logout(mocker):
    """
    Ensure the left pane updates to the logged out state.
    """
    w = Window(QApplication.clipboard())
    w.left_pane = mocker.MagicMock()
    w.top_pane = mocker.MagicMock()

    w.logout()

    w.left_pane.set_logged_out.assert_called_once_with()
    w.top_pane.set_logged_out.assert_called_once_with()
