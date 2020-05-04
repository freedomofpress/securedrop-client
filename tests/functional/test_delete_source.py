"""
Functional tests for deleting a source in the SecureDrop client application.
The tests are based upon the client testing descriptions here:

https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
from flaky import flaky
from PyQt5.QtCore import Qt


@flaky
@pytest.mark.vcr()
def test_delete_source_and_their_docs(functional_test_logged_in_context, qtbot, mocker):
    """
    It's possible to delete a source and see it removed from the UI.
    """
    gui, controller, temmpdir = functional_test_logged_in_context
    qtbot.wait(1000)

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_widgets.keys()))

    qtbot.waitUntil(check_for_sources, timeout=20000)
    source_ids = list(gui.main_view.source_list.source_widgets.keys())
    assert len(source_ids) == 2
    first_source_id = source_ids[0]
    first_source_widget = gui.main_view.source_list.source_widgets[first_source_id]
    qtbot.mouseClick(first_source_widget, Qt.LeftButton)
    qtbot.wait(1000)

    assert gui.main_view.source_list.count() == 2

    # Delete the first source.
    # This is IMPOSSIBLE to trigger via either the qtbot or DeleteSourceAction
    # instance -- hence this "direct" approach. In the end we need to know that
    # the UI is updated once the source is deleted.
    conversation = gui.main_view.view_layout.itemAt(0).widget()
    controller.delete_source(conversation.conversation_title_bar.source)

    def check_source_list():
        # Confirm there is now only one source in the client list.
        assert gui.main_view.source_list.count() == 1

    qtbot.waitUntil(check_source_list, timeout=20000)
