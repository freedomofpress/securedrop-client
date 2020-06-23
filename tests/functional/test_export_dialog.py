"""
Functional tests for sending messages in the SecureDrop client application. The
tests are based upon the client testing descriptions here:

https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
from flaky import flaky
from PyQt5.QtCore import Qt

from securedrop_client.gui.widgets import FileWidget
from tests.conftest import (
    TIME_APP_START,
    TIME_CLICK_ACTION,
    TIME_FILE_DOWNLOAD,
    TIME_RENDER_SOURCE_LIST,
    TIME_SYNC,
)


@flaky
@pytest.mark.vcr()
def test_export_dialog(functional_test_logged_in_context, qtbot, mocker):
    """
    We will download a file received from the source
    the conversation window.
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

    qtbot.wait(TIME_SYNC)
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
    qtbot.wait(TIME_FILE_DOWNLOAD)
    assert file_msg.export_button.isHidden() is False
    assert file_msg.file_name.text() == "hello.txt"
    assert file_msg.file_size.text() == "9B"

    # Let us export
    qtbot.mouseClick(file_msg.export_button, Qt.LeftButton)

    def check_for_export_dialog():
        assert file_msg.export_dialog

    qtbot.waitUntil(check_for_export_dialog, timeout=TIME_CLICK_ACTION)

    export_dialog = file_msg.export_dialog
    qtbot.mouseClick(export_dialog.continue_button, Qt.LeftButton)

    def check_password_form():
        assert export_dialog.passphrase_form.isHidden() is False

    qtbot.waitUntil(check_password_form, timeout=TIME_CLICK_ACTION)

    message = "Use Tor Browser"
    # Focus on passphrase box text entry.
    qtbot.mouseClick(export_dialog.passphrase_field, Qt.LeftButton)
    # Type in a message to the passphrase box.
    qtbot.keyClicks(export_dialog.passphrase_field, message)
    qtbot.wait(TIME_CLICK_ACTION)

    # click on the continue button
    qtbot.mouseClick(export_dialog.continue_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)

    assert export_dialog.continue_button.text() == "DONE"
