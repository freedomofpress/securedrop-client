"""
Functional tests for downloading files in the SecureDrop client.

The tests are based upon the client testing descriptions here:
https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
from flaky import flaky
from PyQt5.QtCore import Qt

from securedrop_client.gui.widgets import FileWidget
from tests.conftest import (
    TIME_CLICK_ACTION,
    TIME_FILE_DOWNLOAD,
    TIME_RENDER_CONV_VIEW,
    TIME_RENDER_SOURCE_LIST,
)


@flaky
@pytest.mark.vcr()
def test_download_file(functional_test_logged_in_context, qtbot, mocker):
    """
    Verify the expected file name and file size when a file is downloaded and that the export and
    print buttons become visible.
    """
    gui, controller = functional_test_logged_in_context

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_items.keys()))

    # Select the last first in the source list
    qtbot.waitUntil(check_for_sources, timeout=TIME_RENDER_SOURCE_LIST)
    source_ids = list(gui.main_view.source_list.source_items.keys())
    first_source_item = gui.main_view.source_list.source_items[source_ids[0]]
    first_source_widget = gui.main_view.source_list.itemWidget(first_source_item)
    qtbot.mouseClick(first_source_widget, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)

    def conversation_with_file_is_rendered():
        assert gui.main_view.view_layout.itemAt(0)
        conversation = gui.main_view.view_layout.itemAt(0).widget()
        assert conversation
        file_id = list(conversation.conversation_view.current_messages.keys())[-1]
        file_widget = conversation.conversation_view.current_messages[file_id]
        assert isinstance(file_widget, FileWidget)

    # Get the selected source conversation that contains a file attachment
    qtbot.waitUntil(conversation_with_file_is_rendered, timeout=TIME_RENDER_CONV_VIEW)
    conversation = gui.main_view.view_layout.itemAt(0).widget()
    file_id = list(conversation.conversation_view.current_messages.keys())[-1]
    file_widget = conversation.conversation_view.current_messages[file_id]

    # Click on the download button for the file
    qtbot.mouseClick(file_widget.download_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.wait(TIME_FILE_DOWNLOAD)

    assert file_widget.export_button.isHidden() is False
    assert file_widget.print_button.isHidden() is False
    assert file_widget.file_name.text() == "hello.txt"
    assert file_widget.file_size.text() == "6B"
