"""
Functional tests for sending replies in offline mode in the SecureDrop client.

The tests are based upon the client testing descriptions here:
https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""

from flaky import flaky
from PyQt5.QtCore import Qt

from securedrop_client.gui.widgets import SourceConversationWrapper
from tests.conftest import TIME_CLICK_ACTION, TIME_RENDER_CONV_VIEW, TIME_RENDER_SOURCE_LIST


@flaky
def test_offline_send_reply_to_source(functional_test_offline_context, qtbot, mocker):
    """
    Verify that you cannot enter text or send a reply in offline mode.
    """
    gui, controller = functional_test_offline_context

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
        assert gui.main_view.view_layout.currentIndex() == gui.main_view.CONVERSATION_INDEX
        assert isinstance(
            gui.main_view.view_layout.widget(gui.main_view.view_layout.currentIndex()),
            SourceConversationWrapper,
        )

    # Get the selected source conversation
    qtbot.waitUntil(check_for_conversation, timeout=TIME_RENDER_CONV_VIEW)

    conversation = gui.main_view.view_layout.widget(gui.main_view.view_layout.currentIndex())

    assert not conversation.reply_box.text_edit.isEnabled()
    assert not conversation.reply_box.send_button.isVisible()
