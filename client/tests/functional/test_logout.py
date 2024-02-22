"""
Functional test for logging out of the SecureDrop client.

The tests are based upon the client testing descriptions here:
https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""

import pytest
from flaky import flaky

from tests.conftest import TIME_LOGOUT


@flaky
@pytest.mark.vcr()
def test_logout_as_journalist(functional_test_logged_in_context, qtbot, mocker):
    """
    Verify that the login button appears after logging out.
    """
    gui, controller = functional_test_logged_in_context
    assert not gui.left_pane.user_profile.login_button.isVisible()

    # Trigger log out
    # Note: The qtbot object cannot interact with QAction items (as used in the logout button/menu),
    # so we programatically logout rather than using the GUI via qtbot
    gui.left_pane.user_profile.user_button._menu.logout.trigger()

    def login_button_is_visible():
        assert gui.left_pane.user_profile.login_button.isVisible()

    # When the login button appears then we know logout is complete
    qtbot.waitUntil(login_button_is_visible, timeout=TIME_LOGOUT)
