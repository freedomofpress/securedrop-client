"""
Functional tests for starring sources in offline mode in the SecureDrop client.

The tests are based upon the client testing descriptions here:
https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""

from flaky import flaky
from PyQt5.QtCore import Qt

from tests.conftest import TIME_CLICK_ACTION, TIME_RENDER_CONV_VIEW, TIME_RENDER_SOURCE_LIST


@flaky
def test_offline_star_source(functional_test_offline_context, qtbot):
    """
    Verify that starring while in offline mode results in no state change with the star and that
    the expected error appears.
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

    # Store state before attempting to star
    is_starred = first_source_widget.star.is_starred
    is_checked = first_source_widget.star.isChecked()

    # Attempt to star the source
    qtbot.mouseClick(first_source_widget.star, Qt.LeftButton)

    def sign_in_required_error():
        msg = gui.top_pane.error_status_bar.status_bar.currentMessage()
        assert msg == "You must sign in to perform this action."

    qtbot.waitUntil(sign_in_required_error, timeout=TIME_RENDER_CONV_VIEW)

    # Verify that star state did not change
    assert first_source_widget.star.is_starred == is_starred
    assert first_source_widget.star.isChecked() == is_checked
