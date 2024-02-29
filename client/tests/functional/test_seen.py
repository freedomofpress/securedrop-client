"""
Functional tests for testing seen/unseen feature in the SecureDrop client.
"""

from flaky import flaky
from PyQt5.QtCore import Qt

from tests.conftest import TIME_CLICK_ACTION, TIME_RENDER_SOURCE_LIST


@flaky
def test_unseen_source_becomes_seen_on_click(functional_test_logged_in_context, qtbot, mocker):
    """
    Verify that a new message with the expected text shows up in the conversation view.
    """
    gui, controller = functional_test_logged_in_context

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_items.keys()))

    # Select the first source in the source list
    qtbot.waitUntil(check_for_sources, timeout=TIME_RENDER_SOURCE_LIST)
    source_ids = list(gui.main_view.source_list.source_items.keys())
    unseen_source_widget = None
    for source_id in source_ids:
        source_item = gui.main_view.source_list.source_items[source_id]
        source_widget = gui.main_view.source_list.itemWidget(source_item)
        if not source_widget.source.seen:
            unseen_source_widget = source_widget
            assert not unseen_source_widget.seen
            qtbot.mouseClick(source_widget, Qt.LeftButton)
            qtbot.wait(TIME_CLICK_ACTION)
            break

    assert unseen_source_widget.seen


@flaky
def test_seen_and_unseen(functional_test_logged_in_context, qtbot, mocker):
    """
    Verify that a new message with the expected text shows up in the conversation view.
    """
    gui, controller = functional_test_logged_in_context

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_items.keys()))

    # Select the first source in the source list
    qtbot.waitUntil(check_for_sources, timeout=TIME_RENDER_SOURCE_LIST)
    source_ids = list(gui.main_view.source_list.source_items.keys())
    for source_id in source_ids:
        source_item = gui.main_view.source_list.source_items[source_id]
        source_widget = gui.main_view.source_list.itemWidget(source_item)
        if source_widget.source.seen:
            assert source_widget.seen
        else:
            assert not source_widget.seen
