"""
Functional tests for sending messages in the SecureDrop client application. The
tests are based upon the client testing descriptions here:

https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
from flaky import flaky
from PyQt5.QtCore import Qt

from tests.conftest import TIME_APP_START, TIME_CLICK_ACTION, TIME_RENDER_SOURCE_LIST


@flaky
@pytest.mark.vcr()
def test_send_reply_to_source(functional_test_logged_in_context, qtbot, mocker):
    """
    It's possible to send a reply to a source and see it show up in the
    conversation window.
    """
    gui, controller, tempdir = functional_test_logged_in_context
    qtbot.wait(TIME_APP_START)

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_items.keys()))

    qtbot.waitUntil(check_for_sources, timeout=TIME_RENDER_SOURCE_LIST)
    source_ids = list(gui.main_view.source_list.source_items.keys())
    first_source_id = source_ids[0]
    first_source_item = gui.main_view.source_list.source_items[first_source_id]
    first_source_widget = gui.main_view.source_list.itemWidget(first_source_item)
    qtbot.mouseClick(first_source_widget, Qt.LeftButton)
    # Type something into the reply box and click the send button.
    message = "Hello, world!"
    conversation = gui.main_view.view_layout.itemAt(0).widget()
    # Focus on reply box text entry.
    qtbot.mouseClick(conversation.reply_box.text_edit, Qt.LeftButton)
    # Type in a message to the reply box.
    qtbot.keyClicks(conversation.reply_box.text_edit, message)
    qtbot.wait(TIME_CLICK_ACTION)
    # Wait until the result of the click on the send button has caused the
    # reply_sent signal to trigger.
    with qtbot.waitSignal(conversation.reply_box.reply_sent):
        qtbot.mouseClick(conversation.reply_box.send_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    # Ensure the last widget in the conversation view contains the text we
    # just typed.
    last_msg_id = list(conversation.conversation_view.current_messages.keys())[-1]
    last_msg = conversation.conversation_view.current_messages[last_msg_id]
    assert last_msg.message.text() == message
