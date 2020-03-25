"""
Functional test for logging out of the SecureDrop client application. The test
is based upon the client testing descriptions here:

https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
from flaky import flaky
from .utils import get_safe_tempdir, get_logged_in_test_context


@flaky
@pytest.mark.vcr()
def test_logout_as_journalist(qtbot, mocker):
    """
    WARNING: THIS TEST CAUSES SUBSEQUENT TESTS TO CRASH WITH A CORE DUMP!

    As a result it should be run in isolation (see the test-functional section
    of the Makefile for details). Why does it crash? I suspect shared state
    leaking via the qtbot instance passed into tests.

    A journalist can successfully log out of the application.
    """
    totp = "333598"
    tempdir = get_safe_tempdir()
    gui, controller = get_logged_in_test_context(tempdir, qtbot, totp)

    def check_login_button():
        assert gui.left_pane.user_profile.login_button.isVisible()

    # The qtbot object cannot interact with QAction items (as used in the
    # logout button/menu), so we're forced to programatically trigger it
    # rather than pretend some sort of user interaction via the qtbot.
    gui.left_pane.user_profile.user_button.menu.logout.trigger()
    # Wait until the logout button is pressed.
    qtbot.waitUntil(check_login_button, timeout=10000)
