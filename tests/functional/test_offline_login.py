"""
Functional tests for loggin in offline in the SecureDrop client.

The tests are based upon the client testing descriptions here:
https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
from flaky import flaky
from PyQt5.QtCore import Qt

from tests.conftest import PASSWORD, TIME_RENDER_CONV_VIEW, USERNAME


@flaky
@pytest.mark.vcr()
def test_login_from_offline(functional_test_offline_context, qtbot, mocker, totp_code):
    """
    First log in in offline mode, then log in from the main window with credentials, next verify
    that the login was successful by checking that the login dialog is closed.
    """
    gui, controller = functional_test_offline_context

    # Click on login button
    qtbot.mouseClick(gui.left_pane.user_profile.login_button, Qt.LeftButton)

    def check_login_dialog():
        assert gui.login_dialog

    # Log in with credentials
    qtbot.waitUntil(check_login_dialog, timeout=TIME_RENDER_CONV_VIEW)
    qtbot.keyClicks(gui.login_dialog.username_field, USERNAME)
    qtbot.keyClicks(gui.login_dialog.password_field, PASSWORD)
    qtbot.keyClicks(gui.login_dialog.tfa_field, totp_code)
    qtbot.mouseClick(gui.login_dialog.submit, Qt.LeftButton)

    # When the login dialog is closed then we know login is complete.
    def wait_for_login():
        assert gui.login_dialog is None

    qtbot.waitUntil(wait_for_login, timeout=TIME_RENDER_CONV_VIEW)
