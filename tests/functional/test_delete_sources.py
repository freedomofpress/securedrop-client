"""
Functional tests for deleting multiple sources in the SecureDrop client.
"""
import pytest
from flaky import flaky
from PyQt5.QtCore import Qt
from PyQt5.QtWidgets import QCheckBox

from tests.conftest import TIME_CLICK_ACTION, TIME_RENDER_CONV_VIEW, TIME_RENDER_SOURCE_LIST


@flaky
@pytest.mark.vcr()
def test_delete_sources(functional_test_logged_in_context, qtbot, mocker):
    """
    Verify that the source list's size is reduced by two when two sources are deleted.
    """
    gui, controller = functional_test_logged_in_context

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_items.keys())) >= 2

    # Select the first two sources in the source list
    qtbot.waitUntil(check_for_sources, timeout=TIME_RENDER_SOURCE_LIST)
    source_ids = list(gui.main_view.source_list.source_items.keys())
    first_source_item = gui.main_view.source_list.source_items[source_ids[-2]]
    first_source_widget = gui.main_view.source_list.itemWidget(first_source_item)
    first_source_widget_checkbox = first_source_widget.findChild(QCheckBox)
    first_source_widget_checkbox.click()
    second_source_item = gui.main_view.source_list.source_items[source_ids[-1]]
    second_source_widget = gui.main_view.source_list.itemWidget(second_source_item)
    second_source_widget_checkbox = second_source_widget.findChild(QCheckBox)
    second_source_widget_checkbox.click()
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.wait(TIME_CLICK_ACTION)

    # Delete the selected sources
    # Note: The qtbot object cannot interact with QAction items (as used in the delete button/menu)
    # so we programatically delete the source rather than using the GUI via qtbot
    source_count = gui.main_view.source_list.count()
    sources_to_delete = [first_source_widget.source.uuid, second_source_widget.source.uuid]
    controller.delete_sources(sources_to_delete)

    def check_source_list():
        assert gui.main_view.source_list.count() == source_count - 2

    qtbot.waitUntil(check_source_list, timeout=TIME_RENDER_SOURCE_LIST)
