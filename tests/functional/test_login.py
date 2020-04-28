"""
Functional tests for logging into the SecureDrop client application. The tests
are based upon the client testing descriptions here:

https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
from flaky import flaky
from PyQt5.QtCore import Qt

from securedrop_client.gui.main import Window
from securedrop_client.gui.widgets import LoginDialog

from tests.conftest import USERNAME, PASSWORD


def test_login_ensure_errors_displayed(qtbot, mocker):
    """
    We see an error if incomplete credentials are supplied to the login dialog.
    """
    w = Window()
    login_dialog = LoginDialog(w)
    login_dialog.show()
    assert login_dialog.error_bar.error_status_bar.text() == ""
    qtbot.keyClicks(login_dialog.username_field, "journalist")
    qtbot.mouseClick(login_dialog.submit, Qt.LeftButton)
    expected = "Please enter a username, passphrase and two-factor code."
    actual = login_dialog.error_bar.error_status_bar.text()
    assert actual == expected


@flaky
@pytest.mark.vcr()  # Ensure any API network traffic is recorded/replayed.
def test_login_as_journalist(functional_test_logged_out_context, qtbot, mocker):
    """
    The app is visible if the user logs in with apparently correct credentials.
    """
    gui, controller, tempdir = functional_test_logged_out_context
    gui.setup(controller)
    # Fill in UI with good credentials.
    qtbot.keyClicks(gui.login_dialog.username_field, USERNAME)
    qtbot.keyClicks(gui.login_dialog.password_field, PASSWORD)
    qtbot.keyClicks(gui.login_dialog.tfa_field, "493941")
    # The waitSignal context handler is used to allow the API thread to call
    # and then (ultimately) emit the expected signal. This pattern will need to
    # be used with all API calls. For more information about this method, see:
    # https://pytest-qt.readthedocs.io/en/latest/signals.html
    with qtbot.waitSignal(controller.authentication_state, timeout=10000):
        qtbot.mouseClick(gui.login_dialog.submit, Qt.LeftButton)
    # The main window is visible (indicating a successful login).
    assert gui.isVisible()
    # The login box no longer exists.
    assert gui.login_dialog is None
