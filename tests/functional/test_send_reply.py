"""
Functional tests for sending messages in the SecureDrop client application. The
tests are based upon the client testing descriptions here:

https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
from PyQt5.QtCore import Qt
from .utils import get_safe_tempdir, get_logged_in_test_context


@pytest.mark.vcr()
def test_send_reply_to_source(qtbot, mocker):
    """
    It's possible to send a reply to a source and see it show up in the
    conversation window.
    """
    totp = "778326"
    tempdir = get_safe_tempdir()
    gui, controller = get_logged_in_test_context(tempdir, qtbot, totp)
    qtbot.wait(1000)

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_widgets.keys()))

    qtbot.waitUntil(check_for_sources, timeout=10000)
    source_ids = list(gui.main_view.source_list.source_widgets.keys())
    first_source_id = source_ids[0]
    first_source_widget = gui.main_view.source_list.source_widgets[first_source_id]
    qtbot.mouseClick(first_source_widget, Qt.LeftButton)
    # Type something into the reply box and click the send button.
    message = "Hello, world!"
    conversation = gui.main_view.view_layout.itemAt(0).widget()
    # Focus on reply box text entry.
    qtbot.mouseClick(conversation.reply_box.text_edit, Qt.LeftButton)
    # Type in a message to the reply box.
    qtbot.keyClicks(conversation.reply_box.text_edit, message)
    qtbot.wait(1000)
    # Wait until the result of the click on the send button has caused the
    # reply_sent signal to trigger.
    with qtbot.waitSignal(conversation.reply_box.reply_sent):
        qtbot.mouseClick(conversation.reply_box.send_button, Qt.LeftButton)
    qtbot.wait(1000)
    # Ensure the last widget in the conversation view contains the text we
    # just typed.
    last_msg_id = list(conversation.conversation_view.current_messages.keys())[-1]
    last_msg = conversation.conversation_view.current_messages[last_msg_id]
    assert last_msg.message.text() == message
