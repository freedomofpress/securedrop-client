"""
Functional tests for starring/unstarring sources in the SecureDrop client.

The tests are based upon the client testing descriptions here:
https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""

import pytest
from flaky import flaky
from PyQt5.QtCore import Qt

from tests.conftest import TIME_CLICK_ACTION, TIME_RENDER_SOURCE_LIST


@flaky
@pytest.mark.vcr()
def test_star_source(functional_test_logged_in_context, qtbot, mocker):
    """
    Verify that the source is starred after clicking on the star widget and unstarred after clicking
    on it again.
    """
    gui, controller = functional_test_logged_in_context

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_items.keys()))

    # Select the first source in the source list
    qtbot.waitUntil(check_for_sources, timeout=TIME_RENDER_SOURCE_LIST)
    source_ids = list(gui.main_view.source_list.source_items.keys())
    first_source_item = gui.main_view.source_list.source_items[source_ids[0]]
    first_source_widget = gui.main_view.source_list.itemWidget(first_source_item)
    qtbot.mouseClick(first_source_widget, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)

    # Verify that the source is starred after clicking on the star widget
    qtbot.mouseClick(first_source_widget.star, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    assert first_source_widget.star.is_starred is True
    assert first_source_widget.star.isChecked() is True

    # Verify that the source is not starred after clicking on the star widget again
    qtbot.mouseClick(first_source_widget.star, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    assert first_source_widget.star.is_starred is False
    assert first_source_widget.star.isChecked() is False
