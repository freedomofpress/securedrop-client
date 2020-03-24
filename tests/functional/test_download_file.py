"""
Functional tests for sending messages in the SecureDrop client application. The
tests are based upon the client testing descriptions here:

https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
from PyQt5.QtCore import Qt
from securedrop_client.gui.widgets import FileWidget
from .utils import get_safe_tempdir, get_logged_in_test_context


@pytest.mark.vcr()
def test_download_file(qtbot, mocker):
    """
    We will download a file received from the source
    the conversation window.
    """
    totp = "353061"
    tempdir = get_safe_tempdir()
    gui, controller = get_logged_in_test_context(tempdir, qtbot, totp)
    qtbot.wait(1000)

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_widgets.keys()))

    qtbot.waitUntil(check_for_sources, timeout=10000)
    source_ids = list(gui.main_view.source_list.source_widgets.keys())
    first_source_id = source_ids[2]
    first_source_widget = gui.main_view.source_list.source_widgets[first_source_id]
    qtbot.mouseClick(first_source_widget, Qt.LeftButton)

    qtbot.wait(10000)  # Wait for the client to sync.
    # Ensure the last widget in the conversation view contains the expected
    # text from the source.
    conversation = gui.main_view.view_layout.itemAt(0).widget()
    message = "this is the message"
    # We get the file from the source.
    file_msg_id = list(conversation.conversation_view.current_messages.keys())[-1]
    file_msg = conversation.conversation_view.current_messages[file_msg_id]
    assert isinstance(file_msg, FileWidget)
    # We see the source's message.
    last_msg_id = list(conversation.conversation_view.current_messages.keys())[-2]
    last_msg = conversation.conversation_view.current_messages[last_msg_id]
    assert last_msg.message.text() == message

    # Let us download the file
    qtbot.mouseClick(file_msg.download_button, Qt.LeftButton)
    qtbot.wait(5000)
    assert file_msg.export_button.isHidden() is False
    assert file_msg.file_name.text() == "hello.txt"
    assert file_msg.file_size.text() == "9B"
