"""
Functional test for logging out of the SecureDrop client application. The test
is based upon the client testing descriptions here:

https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
from PyQt5.QtCore import Qt
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
    totp = "333598"
    tempdir = get_safe_tempdir()
    gui, controller = get_logged_in_test_context(tempdir, qtbot, totp)

    def check_login_button():
        assert gui.left_pane.user_profile.login_button.isVisible()

    # The qtbot object cannot interact with QAction items (as used in the
    # logout button/menu), so we're forced to programatically trigger it
    # rather than pretend some sort of user interaction via the qtbot.
    with qtbot.waitSignal(gui.left_pane.user_profile.user_button.clicked, timeout=1000):
        gui.left_pane.user_profile.user_button.menu.logout.trigger()
        qtbot.mouseClick(gui.left_pane.user_profile.user_icon, Qt.LeftButton)
    
    
