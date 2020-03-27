"""
Functional test for logging out of the SecureDrop client application. The test
is based upon the client testing descriptions here:

https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
import time
import pyautogui

from .utils import get_safe_tempdir, get_logged_in_test_context


@pytest.mark.vcr()
def test_user_icon_click(qtbot, mocker):
    """
    WARNING: THIS TEST CAUSES SUBSEQUENT TESTS TO CRASH WITH A CORE DUMP!

    As a result it should be run in isolation (see the test-functional section
    of the Makefile for details). Why does it crash? I suspect shared state
    leaking via the qtbot instance passed into tests.

    A journalist can successfully see the logout menu by clicking the user icon.
    """
    totp = "079978"
    tempdir = get_safe_tempdir()
    gui, controller = get_logged_in_test_context(tempdir, qtbot, totp)

    def check_login_button():
        assert gui.left_pane.user_profile.login_button.isVisible()

    qtbot.wait(5000)
    # Now instead of clicking via qtbot, we can click via mouse
    pyautogui.click(25, 70)
    # # Now we should have the menu open
    # Also means qtbot if of no use right now
    time.sleep(0.5)
    # Let us click on the signout button
    pyautogui.click(87, 100)
    # Here the eventloop is back with qtbot
    qtbot.waitUntil(check_login_button, timeout=10000)
