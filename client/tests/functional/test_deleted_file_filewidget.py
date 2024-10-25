"""
Functional test for ensuring attempting to access a deleted File's database record
deletes the FileWidget instead of causing a crash. This is an edge case that could occur
upon a conflict between downloading a file and deleting a source or conversation.

The tests are based upon the client testing descriptions here:
https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""

from flaky import flaky
from PyQt5.QtCore import Qt

from securedrop_client.gui.widgets import FileWidget, SourceConversationWrapper
from tests.conftest import (
    TIME_CLICK_ACTION,
    TIME_RENDER_CONV_VIEW,
    TIME_RENDER_SOURCE_LIST,
)


@flaky
def test_deleted_file_filewidget(functional_test_logged_in_context, qtbot, mocker):
    """
    Ensure that, if a File record is deleted from the database after a corresponding widget
    has been rendered, the app handles the deletion gracefully and deletes the orphaned widget.
    """
    gui, controller = functional_test_logged_in_context

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_items.keys()))

    # Select the last first in the source list
    qtbot.waitUntil(check_for_sources, timeout=TIME_RENDER_SOURCE_LIST)

    # Select the second source in the list to avoid marking unseen sources as seen
    source_id = list(gui.main_view.source_list.source_items.keys())[1]
    source_item = gui.main_view.source_list.source_items[source_id]
    source_widget = gui.main_view.source_list.itemWidget(source_item)
    qtbot.mouseClick(source_widget, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)

    def conversation_with_file_is_rendered():
        assert gui.main_view.view_layout.currentIndex() == gui.main_view.CONVERSATION_INDEX
        conversation = gui.main_view.view_layout.widget(gui.main_view.view_layout.currentIndex())
        assert isinstance(conversation, SourceConversationWrapper)
        file_id = list(conversation.conversation_view.current_messages.keys())[2]
        file_widget = conversation.conversation_view.current_messages[file_id]
        assert isinstance(file_widget, FileWidget)

    # Get the selected source conversation that contains a file attachment
    qtbot.waitUntil(conversation_with_file_is_rendered, timeout=TIME_RENDER_CONV_VIEW)
    conversation = gui.main_view.view_layout.widget(gui.main_view.view_layout.currentIndex())
    file_id = list(conversation.conversation_view.current_messages.keys())[2]
    file_widget = conversation.conversation_view.current_messages[file_id]

    deleteLater = mocker.patch.object(file_widget, "deleteLater")

    # Delete the file from the database to simulate a conflict between sync (deletion)
    # and the widget
    controller.session.delete(file_widget.file)
    controller.session.commit()

    # Click on the download button for the file
    qtbot.mouseClick(file_widget.download_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)

    deleteLater.assert_called_once()
