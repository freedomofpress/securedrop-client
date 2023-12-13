"""
Functional tests for deleting a source in the SecureDrop client.

The tests are based upon the client testing descriptions here:
https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
from flaky import flaky
from PyQt5.QtCore import Qt

from tests.conftest import TIME_CLICK_ACTION, TIME_RENDER_CONV_VIEW, TIME_RENDER_SOURCE_LIST


@flaky
@pytest.mark.vcr()
def test_delete_source(functional_test_logged_in_context, qtbot, mocker):
    """
    Verify that the source list's size is reduced by one when a source is deleted.
    """
    gui, controller = functional_test_logged_in_context

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_items.keys()))

    # Select the first source in the source list
    qtbot.waitUntil(check_for_sources, timeout=TIME_RENDER_SOURCE_LIST)
    source_ids = list(gui.main_view.source_list.source_items.keys())
    first_source_item = gui.main_view.source_list.source_items[source_ids[-1]]
    first_source_widget = gui.main_view.source_list.itemWidget(first_source_item)
    qtbot.mouseClick(first_source_widget, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)

    def check_for_conversation():
        assert gui.main_view.view_layout.itemAt(0)
        assert gui.main_view.view_layout.itemAt(0).widget()

    # Get the selected source conversation
    qtbot.waitUntil(check_for_conversation, timeout=TIME_RENDER_CONV_VIEW)
    conversation = gui.main_view.view_layout.itemAt(0).widget()

    # Delete the selected source
    # Note: The qtbot object cannot interact with QAction items (as used in the delete button/menu)
    # so we programatically delete the source rather than using the GUI via qtbot
    source_count = gui.main_view.source_list.count()
    controller.delete_source(conversation.conversation_title_bar.source)

    def check_source_list():
        assert gui.main_view.source_list.count() == source_count - 1

    qtbot.waitUntil(check_source_list, timeout=TIME_RENDER_SOURCE_LIST)
