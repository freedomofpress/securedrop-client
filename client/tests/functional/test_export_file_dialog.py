"""
Functional tests for exporting files in the SecureDrop client.

The tests are based upon the client testing descriptions here:
https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
from flaky import flaky
from PyQt5.QtCore import Qt

from securedrop_client.gui.widgets import FileWidget, SourceConversationWrapper
from tests.conftest import (
    TIME_CLICK_ACTION,
    TIME_FILE_DOWNLOAD,
    TIME_RENDER_CONV_VIEW,
    TIME_RENDER_EXPORT_DIALOG,
    TIME_RENDER_SOURCE_LIST,
)


def _setup_export(functional_test_logged_in_context, qtbot, mocker, mock_export_service):
    """
    Helper. Set up export test context and return reference to export dialog.
    """
    mocker.patch(
        "securedrop_client.gui.widgets.export.getService", return_value=mock_export_service
    )

    gui, controller = functional_test_logged_in_context

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_items.keys()))

    # Select the first source in the source list
    qtbot.waitUntil(check_for_sources, timeout=TIME_RENDER_SOURCE_LIST)

    # Select the second source in the list to avoid marking unseen sources as seen
    source_id = list(gui.main_view.source_list.source_items.keys())[1]
    source_item = gui.main_view.source_list.source_items[source_id]
    source_widget = gui.main_view.source_list.itemWidget(source_item)
    qtbot.mouseClick(source_widget, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)

    def conversation_with_file_is_rendered():
        assert gui.main_view.view_layout.itemAt(0)
        conversation = gui.main_view.view_layout.itemAt(0).widget()
        assert isinstance(conversation, SourceConversationWrapper)
        file_id = list(conversation.conversation_view.current_messages.keys())[2]
        file_widget = conversation.conversation_view.current_messages[file_id]
        assert isinstance(file_widget, FileWidget)

    # Get the selected source conversation that contains a file attachment
    qtbot.waitUntil(conversation_with_file_is_rendered, timeout=TIME_RENDER_CONV_VIEW)
    conversation = gui.main_view.view_layout.itemAt(0).widget()
    file_id = list(conversation.conversation_view.current_messages.keys())[2]
    file_widget = conversation.conversation_view.current_messages[file_id]

    # If the file is not downloaded, click on the download button
    if file_widget.download_button.isVisible():
        qtbot.mouseClick(file_widget.download_button, Qt.LeftButton)
        qtbot.wait(TIME_CLICK_ACTION)
        qtbot.wait(TIME_FILE_DOWNLOAD)

    def check_for_export_dialog():
        assert file_widget.export_dialog

    # Begin exporting the file
    qtbot.mouseClick(file_widget.export_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.waitUntil(check_for_export_dialog, timeout=TIME_RENDER_EXPORT_DIALOG)

    return file_widget.export_dialog


@flaky
@pytest.mark.vcr()
def test_export_file_dialog(functional_test_logged_in_context, qtbot, mocker, mock_export_service):
    """
    Download a file, export it, and verify that the export is complete by checking that the label of
    the export dialog's continue button is "DONE".
    """
    mocker.patch(
        "securedrop_client.gui.widgets.export.getService", return_value=mock_export_service
    )

    gui, controller = functional_test_logged_in_context

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_items.keys()))

    # Select the first source in the source list
    qtbot.waitUntil(check_for_sources, timeout=TIME_RENDER_SOURCE_LIST)

    # Select the second source in the list to avoid marking unseen sources as seen
    source_id = list(gui.main_view.source_list.source_items.keys())[1]
    source_item = gui.main_view.source_list.source_items[source_id]
    source_widget = gui.main_view.source_list.itemWidget(source_item)
    qtbot.mouseClick(source_widget, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)

    def conversation_with_file_is_rendered():
        assert gui.main_view.view_layout.itemAt(0)
        conversation = gui.main_view.view_layout.itemAt(0).widget()
        assert isinstance(conversation, SourceConversationWrapper)
        file_id = list(conversation.conversation_view.current_messages.keys())[2]
        file_widget = conversation.conversation_view.current_messages[file_id]
        assert isinstance(file_widget, FileWidget)

    # Get the selected source conversation that contains a file attachment
    qtbot.waitUntil(conversation_with_file_is_rendered, timeout=TIME_RENDER_CONV_VIEW)
    conversation = gui.main_view.view_layout.itemAt(0).widget()
    file_id = list(conversation.conversation_view.current_messages.keys())[2]
    file_widget = conversation.conversation_view.current_messages[file_id]

    # If the file is not downloaded, click on the download button
    if file_widget.download_button.isVisible():
        qtbot.mouseClick(file_widget.download_button, Qt.LeftButton)
        qtbot.wait(TIME_CLICK_ACTION)
        qtbot.wait(TIME_FILE_DOWNLOAD)

    def check_for_export_dialog():
        assert file_widget.export_dialog

    # Begin exporting the file
    qtbot.mouseClick(file_widget.export_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.waitUntil(check_for_export_dialog, timeout=TIME_RENDER_EXPORT_DIALOG)
    export_dialog = file_widget.export_dialog

    def check_password_form():
        assert export_dialog.passphrase_form.isHidden() is False

    # Continue exporting the file
    qtbot.mouseClick(export_dialog.continue_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.waitUntil(check_password_form, timeout=TIME_CLICK_ACTION)

    # Continue exporting the file by entering a passphrase
    qtbot.mouseClick(export_dialog.passphrase_field, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.keyClicks(export_dialog.passphrase_field, "Passphrase Field")
    qtbot.mouseClick(export_dialog.continue_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)

    # Verify export is complete by checking that the continue button says "DONE"
    assert export_dialog.continue_button.text() == "DONE"


@flaky
@pytest.mark.vcr()
def test_export_file_dialog_device_already_unlocked(
    functional_test_logged_in_context, qtbot, mocker, mock_export_service_unlocked_device
):
    """
    Download a file, export it, and verify that the export is complete by checking that the label of
    the export dialog's continue button is "DONE".
    """
    export_dialog = _setup_export(
        functional_test_logged_in_context, qtbot, mocker, mock_export_service_unlocked_device
    )

    def check_skip_password_prompt_for_unlocked_device():
        assert export_dialog.passphrase_form.isHidden() is True
        # todo say something else about the export only screen

    # Continue exporting the file
    qtbot.mouseClick(export_dialog.continue_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.waitUntil(check_skip_password_prompt_for_unlocked_device, timeout=TIME_CLICK_ACTION)

    # Click continue to export the file (skips password prompt screen)
    qtbot.mouseClick(export_dialog.continue_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)

    # Verify export is complete by checking that the continue button says "DONE"
    assert export_dialog.continue_button.text() == "DONE"
