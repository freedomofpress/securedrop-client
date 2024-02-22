"""
Functional tests for logging into the SecureDrop client.

The tests are based upon the client testing descriptions here:
https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""

import pytest
from flaky import flaky
from PyQt5.QtCore import Qt

from tests.conftest import PASSWORD, TIME_CLICK_ACTION, TIME_RENDER_CONV_VIEW, TOTP, USERNAME


def test_login_ensure_errors_displayed(functional_test_app_started_context, qtbot, mocker):
    """
    Verify the error message in the error status bar when incomplete credentials are submitted via
    the login dialog.
    """
    gui, controller = functional_test_app_started_context

    assert gui.login_dialog.error_bar.error_status_bar.text() == ""

    qtbot.keyClicks(gui.login_dialog.username_field, "journalist")
    qtbot.mouseClick(gui.login_dialog.submit, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)

    error_status_msg = gui.login_dialog.error_bar.error_status_bar.text()
    assert error_status_msg == "Please enter a username, passphrase and two-factor code."


@flaky
@pytest.mark.vcr()
def test_login_as_journalist(functional_test_app_started_context, qtbot, mocker):
    """
    Log in from the login dialog with credentials and verify that the login was successful by
    checking that the login dialog is closed and the main window is visible.
    """
    gui, controller = functional_test_app_started_context

    # Log in from the login dialog and wait for the authentication_state signal from the controller
    # to be emitted, which indicates the user authentication state has changed successfully
    qtbot.keyClicks(gui.login_dialog.username_field, USERNAME)
    qtbot.keyClicks(gui.login_dialog.password_field, PASSWORD)
    qtbot.keyClicks(gui.login_dialog.tfa_field, TOTP)
    with qtbot.waitSignal(controller.authentication_state, timeout=TIME_RENDER_CONV_VIEW):
        qtbot.mouseClick(gui.login_dialog.submit, Qt.LeftButton)
        qtbot.wait(TIME_CLICK_ACTION)

    # When the main window is visible and the login dialog is closed then we know login is complete
    assert gui.isVisible()
    assert gui.login_dialog is None
