"""
Functional test for logging out and then login again from offline mode.
"""
import pytest
from PyQt5.QtCore import Qt
from .utils import get_safe_tempdir, get_logged_in_test_context, USERNAME, PASSWORD


@pytest.mark.vcr()
def test_login_from_offline(qtbot, mocker):
    """
    WARNING: THIS TEST CAUSES SUBSEQUENT TESTS TO CRASH WITH A CORE DUMP!

    As a result it should be run in isolation (see the test-functional section
    of the Makefile for details). Why does it crash? I suspect shared state
    leaking via the qtbot instance passed into tests.

    A journalist can successfully log out of the application.
    """
    totp = "805168"
    tempdir = get_safe_tempdir()
    gui, controller = get_logged_in_test_context(tempdir, qtbot, totp)

    qtbot.wait(2000)

    def check_login_button():
        assert gui.left_pane.user_profile.login_button.isVisible()

    # The qtbot object cannot interact with QAction items (as used in the
    # logout button/menu), so we're forced to programatically trigger it
    # rather than pretend some sort of user interaction via the qtbot.
    gui.left_pane.user_profile.user_button.menu.logout.trigger()
    # Wait until the logout button is pressed.
    qtbot.waitUntil(check_login_button, timeout=10000)

    def check_login_dialog():
        assert gui.login_dialog

    qtbot.mouseClick(gui.left_pane.user_profile.login_button, Qt.LeftButton)
    qtbot.waitUntil(check_login_dialog, timeout=10000)

    qtbot.keyClicks(gui.login_dialog.username_field, USERNAME)
    qtbot.keyClicks(gui.login_dialog.password_field, PASSWORD)
    qtbot.keyClicks(gui.login_dialog.tfa_field, "560276")

    qtbot.mouseClick(gui.login_dialog.submit, Qt.LeftButton)

    def wait_for_login():
        assert gui.login_dialog is None

    qtbot.waitUntil(wait_for_login, timeout=10000)
