"""
Functional tests for sending messages in the SecureDrop client application. The
tests are based upon the client testing descriptions here:

https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
from flaky import flaky
from PyQt5.QtCore import Qt


@flaky
@pytest.mark.vcr()
def test_offline_read_conversations(functional_test_logged_in_context, qtbot, mocker):
    """
    It's possible to read downloaded conversations when offline.
    """
    gui, controller, tempdir = functional_test_logged_in_context
    qtbot.wait(1000)

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_widgets.keys()))

    qtbot.waitUntil(check_for_sources, timeout=10000)
    source_ids = list(gui.main_view.source_list.source_widgets.keys())
    first_source_id = source_ids[0]
    first_source_widget = gui.main_view.source_list.source_widgets[first_source_id]
    qtbot.mouseClick(first_source_widget, Qt.LeftButton)

    # Otherwise our test is running too fast to create all files/directories
    # as received via API call.
    qtbot.wait(1000)

    # Now logout.
    def check_login_button():
        assert gui.left_pane.user_profile.login_button.isVisible()

    gui.left_pane.user_profile.user_button.menu.logout.trigger()
    qtbot.waitUntil(check_login_button, timeout=10000)

    # Ensure that clicking on a source shows a conversation that contains
    # activity.
    second_source_id = source_ids[1]
    second_source_widget = gui.main_view.source_list.source_widgets[second_source_id]
    qtbot.mouseClick(second_source_widget, Qt.LeftButton)
    conversation = gui.main_view.view_layout.itemAt(0).widget()
    assert len(list(conversation.conversation_view.current_messages.keys())) > 0
