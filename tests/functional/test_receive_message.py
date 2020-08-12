"""
Functional tests for receiving messages in the SecureDrop client.

The tests are based upon the client testing descriptions here:
https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
from flaky import flaky
from PyQt5.QtCore import Qt

from tests.conftest import TIME_CLICK_ACTION, TIME_RENDER_CONV_VIEW, TIME_RENDER_SOURCE_LIST


@flaky
@pytest.mark.vcr()
def test_receive_message_from_source(functional_test_logged_in_context, qtbot, mocker):
    """
    Verify that a new message with the expected text shows up in the conversation view.
    """
    gui, controller = functional_test_logged_in_context

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_items.keys()))

    # Select the first source in the source list
    qtbot.waitUntil(check_for_sources, timeout=TIME_RENDER_SOURCE_LIST)
    source_ids = list(gui.main_view.source_list.source_items.keys())
    first_source_item = gui.main_view.source_list.source_items[source_ids[0]]
    first_source_widget = gui.main_view.source_list.itemWidget(first_source_item)
    qtbot.mouseClick(first_source_widget, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)

    def check_for_conversation():
        assert gui.main_view.view_layout.itemAt(0)
        assert gui.main_view.view_layout.itemAt(0).widget()

    # Get the selected source conversation
    qtbot.waitUntil(check_for_conversation, timeout=TIME_RENDER_CONV_VIEW)
    conversation = gui.main_view.view_layout.itemAt(0).widget()
    message_id = list(conversation.conversation_view.current_messages.keys())[0]
    message = conversation.conversation_view.current_messages[message_id]

    assert message.message.text() == "this is the message"
