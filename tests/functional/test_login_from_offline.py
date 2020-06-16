"""
Functional test for logging out and then login again from offline mode.
"""
import pytest
from flaky import flaky
from PyQt5.QtCore import Qt

from tests.conftest import PASSWORD, TIME_APP_START, TIME_RENDER_CONV_VIEW, USERNAME


@flaky
@pytest.mark.vcr()
def test_login_from_offline(functional_test_logged_in_context, qtbot, mocker):
    """
    WARNING: THIS TEST CAUSES SUBSEQUENT TESTS TO CRASH WITH A CORE DUMP!

    As a result it should be run in isolation (see the test-functional section
    of the Makefile for details). Why does it crash? I suspect shared state
    leaking via the qtbot instance passed into tests.

    A journalist can successfully log out of the application.
    """
    gui, controller, tempdir = functional_test_logged_in_context
    qtbot.wait(TIME_APP_START)

    def check_login_button():
        assert gui.left_pane.user_profile.login_button.isVisible()

    # The qtbot object cannot interact with QAction items (as used in the
    # logout button/menu), so we're forced to programatically trigger it
    # rather than pretend some sort of user interaction via the qtbot.
    gui.left_pane.user_profile.user_button.menu.logout.trigger()
    # Wait until the logout button is pressed.
    qtbot.waitUntil(check_login_button, timeout=TIME_RENDER_CONV_VIEW)

    def check_login_dialog():
        assert gui.login_dialog

    qtbot.mouseClick(gui.left_pane.user_profile.login_button, Qt.LeftButton)
    qtbot.waitUntil(check_login_dialog, timeout=TIME_RENDER_CONV_VIEW)

    qtbot.keyClicks(gui.login_dialog.username_field, USERNAME)
    qtbot.keyClicks(gui.login_dialog.password_field, PASSWORD)
    qtbot.keyClicks(gui.login_dialog.tfa_field, "560276")

    qtbot.mouseClick(gui.login_dialog.submit, Qt.LeftButton)

    def wait_for_login():
        assert gui.login_dialog is None

    qtbot.waitUntil(wait_for_login, timeout=TIME_RENDER_CONV_VIEW)
