"""
Functional tests for deleting one or more sources in the SecureDrop client.

The tests are based upon the client testing descriptions here:
https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""

import random

import pytest
from flaky import flaky
from PyQt5.QtCore import Qt

from securedrop_client.gui.source.delete import dialog as DialogModule
from securedrop_client.gui.widgets import MultiSelectView, SourceConversationWrapper
from tests.conftest import (
    TIME_CLICK_ACTION,
    TIME_RENDER_CONV_VIEW,
    TIME_RENDER_SOURCE_LIST,
    TIME_SYNC,
)


@pytest.mark.parametrize("num_to_delete", [1, 3])
@flaky
def test_delete_sources(functional_test_logged_in_context, qtbot, mocker, num_to_delete):
    """
    Check that sources selected for deletion are first confirmed and then
    removed from the source list.
    """
    gui, controller = functional_test_logged_in_context

    # Wait for a full sync to give us a stable source list.
    qtbot.wait(TIME_SYNC)

    def check_for_sources():
        """Check that we have enough sources to work with."""
        assert len(list(gui.main_view.source_list.source_items.keys())) >= num_to_delete

    qtbot.waitUntil(check_for_sources, timeout=TIME_RENDER_SOURCE_LIST)

    # Select num_to_delete sources at random.
    source_uuids_to_delete = random.sample(
        sorted(gui.main_view.source_list.source_items), num_to_delete
    )
    for i, source_uuid in enumerate(source_uuids_to_delete):
        source_item = gui.main_view.source_list.source_items[source_uuid]
        source_widget = gui.main_view.source_list.itemWidget(source_item)

        # Simulate a non-<Ctrl> initial click...
        if i == 0:
            qtbot.mouseClick(source_widget, Qt.LeftButton)
        # ...followed by subsequent <Ctrl>-clicks.
        else:
            qtbot.mouseClick(
                source_widget, Qt.LeftButton, modifier=Qt.KeyboardModifier.ControlModifier
            )

        qtbot.wait(TIME_CLICK_ACTION)

    def check_for_conversation():
        """
        Check that the GUI is showing the right view for the number of
        sources selected.
        """
        if num_to_delete == 1:
            index = gui.main_view.CONVERSATION_INDEX
            widget = SourceConversationWrapper
        else:
            index = gui.main_view.MULTI_SELECTED_INDEX
            widget = MultiSelectView

        assert gui.main_view.view_layout.currentIndex() == index
        assert isinstance(
            gui.main_view.view_layout.widget(gui.main_view.view_layout.currentIndex()), widget
        )

    qtbot.waitUntil(check_for_conversation, timeout=TIME_RENDER_CONV_VIEW)

    # Delete the selected source.  We can't qtbot.mouseClick() on a QAction, but
    # we can trigger it directly.
    gui.main_view.top_pane.batch_actions.toolbar.delete_sources_action.trigger()

    def check_and_accept_dialog():
        """Check that the dialog confirms deletion of all sources selected."""
        dialog = (
            gui.main_view.top_pane.batch_actions.toolbar._last_dialog
        )  # FIXME: workaround for #2273
        assert set(source_uuids_to_delete) == {source.uuid for source in dialog.sources}
        dialog.accept()

    qtbot.waitUntil(check_and_accept_dialog, timeout=TIME_CLICK_ACTION)

    def check_source_list():
        """
        Check that all of the sources selected for deletion have been removed
        from the source list.
        """
        for source_uuid in source_uuids_to_delete:
            assert source_uuid not in gui.main_view.source_list.source_items

    qtbot.waitUntil(check_source_list, timeout=TIME_RENDER_SOURCE_LIST)


@flaky
def test_confirm_before_deleting_lots_of_sources(
    functional_test_logged_in_context, qtbot, mocker, monkeypatch
):
    """
    Reduction of test_delete_sources(): With LOTS_OF_SOURCES = num_sources - 1,
    check that the dialog's "continue" button is disabled until the (displayed)
    countdown timer finishes.
    """
    gui, controller = functional_test_logged_in_context

    # Wait for a full sync to give us a stable source list.
    qtbot.wait(TIME_SYNC)
    source_uuids = list(gui.main_view.source_list.source_items.keys())
    num_sources = len(source_uuids)
    monkeypatch.setattr(DialogModule, "LOTS_OF_SOURCES", num_sources - 1)

    for i, source_uuid in enumerate(source_uuids):
        source_item = gui.main_view.source_list.source_items[source_uuid]
        source_widget = gui.main_view.source_list.itemWidget(source_item)

        # Simulate a non-<Ctrl> initial click...
        if i == 0:
            qtbot.mouseClick(source_widget, Qt.LeftButton)
        # ...followed by subsequent <Ctrl>-clicks.
        else:
            qtbot.mouseClick(
                source_widget, Qt.LeftButton, modifier=Qt.KeyboardModifier.ControlModifier
            )

        qtbot.wait(TIME_CLICK_ACTION)

    # Delete the selected source.  We can't qtbot.mouseClick() on a QAction, but
    # we can trigger it directly.
    gui.main_view.top_pane.batch_actions.toolbar.delete_sources_action.trigger()

    def check_and_accept_dialog(ready):
        """Check that the dialog confirms deletion of all sources selected."""
        dialog = (
            gui.main_view.top_pane.batch_actions.toolbar._last_dialog
        )  # FIXME: workaround for #2273
        assert set(source_uuids) == {source.uuid for source in dialog.sources}

        assert dialog.continue_button.isEnabled() == ready
        if ready:
            dialog.accept()
        else:
            assert "wait" in dialog.continue_button.text()

    check_and_accept_dialog(False)

    qtbot.waitUntil(
        lambda: check_and_accept_dialog(True), timeout=DialogModule.CONTINUE_BUTTON_DELAY
    )
