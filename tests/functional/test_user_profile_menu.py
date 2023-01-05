"""
Functional test for logging out of the SecureDrop client.

The test is based upon the client testing descriptions here:
https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pyautogui
import pytest
from flaky import flaky

from tests.conftest import TIME_CLICK_ACTION


@flaky(max_runs=3)
@pytest.mark.vcr()
def test_user_icon_click(qtbot, mocker, functional_test_logged_in_context):
    """
    Verify a journalist can successfully see the logout menu by clicking the user icon of the
    UserProfile widget.
    """
    gui, controller = functional_test_logged_in_context

    # Click the user icon
    user_icon_position = gui.left_pane.user_profile.user_icon.pos()
    point = gui.left_pane.user_profile.user_button.mapToGlobal(user_icon_position)
    cursor_x, cursor_y = point.x(), point.y()
    pyautogui.click(cursor_x, cursor_y)

    def user_menu_is_visible():
        assert gui.left_pane.user_profile.user_button._menu.logout.isVisible()

    # Ensure user menu is visible after clicking on the user icon
    qtbot.waitUntil(user_menu_is_visible, timeout=TIME_CLICK_ACTION)

    # Click the logout option in the user menu
    # Note: Both Qt and PyAutoGUI use a coordinate system with (0, 0) at the top, left screen
    # position. Since the sign out menu appears to the lower right of the user button of the
    # UserProfile widget, we want to move in the positive x-direction and positive y-direction.
    button_width = gui.left_pane.user_profile.user_button.width()
    button_height = gui.left_pane.user_profile.user_button.height()
    pyautogui.click(cursor_x + button_width / 2, cursor_y + button_height)

    def login_button_is_visible():
        assert gui.left_pane.user_profile.login_button.isVisible()

    # When the login button appears then we know logout is complete
    qtbot.waitUntil(login_button_is_visible, timeout=TIME_CLICK_ACTION)
