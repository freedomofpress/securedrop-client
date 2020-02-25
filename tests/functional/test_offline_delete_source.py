"""
Functional tests for deleting a source in the SecureDrop client application.
The tests are based upon the client testing descriptions here:

https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
from PyQt5.QtCore import Qt
from .utils import get_safe_tempdir, get_logged_in_test_context


@pytest.mark.vcr()
def test_offline_delete_source_and_their_docs(qtbot, mocker):
    """
    It's NOT possible to delete a source when the client is offline.
    """
    totp = "533069"
    tempdir = get_safe_tempdir()
    gui, controller = get_logged_in_test_context(tempdir, qtbot, totp)
    qtbot.wait(1000)

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_widgets.keys()))

    qtbot.waitUntil(check_for_sources, timeout=10000)
    source_ids = list(gui.main_view.source_list.source_widgets.keys())
    assert len(source_ids) == 2
    first_source_id = source_ids[0]
    first_source_widget = gui.main_view.source_list.source_widgets[first_source_id]
    qtbot.mouseClick(first_source_widget, Qt.LeftButton)
    qtbot.wait(1000)

    # Now logout.
    def check_login_button():
        assert gui.left_pane.user_profile.login_button.isVisible()

    gui.left_pane.user_profile.user_button.menu.logout.trigger()
    qtbot.waitUntil(check_login_button, timeout=10000)

    # Delete the first source.
    # This is IMPOSSIBLE to trigger via either the qtbot or DeleteSourceAction
    # instance -- hence this "direct" approach. In the end we need to know that
    # the UI is updated once the source is deleted.
    conversation = gui.main_view.view_layout.itemAt(0).widget()
    controller.delete_source(conversation.conversation_title_bar.source)

    def check_for_error():
        # Confirm the user interface is showing a sign-in error.
        msg = gui.top_pane.error_status_bar.status_bar.currentMessage()
        assert msg == 'You must sign in to perform this action.'

    qtbot.waitUntil(check_for_error, timeout=10000)
