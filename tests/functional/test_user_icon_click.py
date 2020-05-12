"""
Functional test for logging out of the SecureDrop client application. The test
is based upon the client testing descriptions here:

https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
import pyautogui

from tests.conftest import TIME_APP_START, TIME_CLICK_ACTION


@pytest.mark.vcr()
def test_user_icon_click(qtbot, mocker, functional_test_logged_in_context):
    """
    WARNING: THIS TEST CAUSES SUBSEQUENT TESTS TO CRASH WITH A CORE DUMP!

    As a result it should be run in isolation (see the test-functional section
    of the Makefile for details). Why does it crash? I suspect shared state
    leaking via the qtbot instance passed into tests.

    A journalist can successfully see the logout menu by clicking the user icon.
    """
    gui, controller, tempdir = functional_test_logged_in_context
    qtbot.wait(TIME_APP_START)

    # Now instead of clicking via qtbot, we can click via mouse
    user_button_position = gui.left_pane.user_profile.user_button.pos()
    point = gui.left_pane.user_profile.user_button.mapToGlobal(user_button_position)
    cursor_x, cursor_y = point.x(), point.y()
    pyautogui.click(cursor_x, cursor_y)

    # Ensure QMenu is visible after the completed click.
    def check_menu_appears():
        assert gui.left_pane.user_profile.user_button.menu.logout.isVisible()

    qtbot.waitUntil(check_menu_appears, timeout=TIME_CLICK_ACTION)

    button_width = gui.left_pane.user_profile.user_button.width()
    button_height = gui.left_pane.user_profile.user_button.height()

    # Both Qt and PyAutoGUI use a coordinate system with (0, 0) at the top, left
    # screen position. Since the sign out menu appears to the lower right of the
    # button, we want to move in the positive x-direction and positive y-direction.
    pyautogui.click(cursor_x + button_width / 2, cursor_y + button_height)

    # Here the eventloop is back with qtbot
    def check_login_button():
        assert gui.left_pane.user_profile.login_button.isVisible()

    qtbot.waitUntil(check_login_button, timeout=TIME_CLICK_ACTION)
