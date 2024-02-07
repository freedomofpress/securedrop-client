"""
Functional tests for exporting files in the SecureDrop client.

The tests are based upon the client testing descriptions here:
https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
from PyQt5.QtCore import Qt

from securedrop_client.gui.conversation.export.export_wizard_page import (
    ErrorPage,
    FinalPage,
    InsertUSBPage,
    PassphraseWizardPage,
    PreflightPage,
)
from securedrop_client.gui.widgets import FileWidget, SourceConversationWrapper
from tests.conftest import (
    TIME_CLICK_ACTION,
    TIME_FILE_DOWNLOAD,
    TIME_RENDER_CONV_VIEW,
    TIME_RENDER_EXPORT_WIZARD,
    TIME_RENDER_SOURCE_LIST,
)


def _setup_export(functional_test_logged_in_context, qtbot, mocker, mock_export):
    """
    Helper. Set up export test context and return reference to export wizard.
    Returns wizard on first page (Preflight warning page).
    """
    mocker.patch(
        "securedrop_client.export.Export.run_export_preflight_checks",
        return_value=mock_export.run_export_preflight_checks,
    )
    mocker.patch("securedrop_client.export.Export.export", return_value=mock_export.export)

    gui, controller = functional_test_logged_in_context

    def check_for_sources():
        assert list(gui.main_view.source_list.source_items) != []

    # Select the first source in the source list
    qtbot.waitUntil(check_for_sources, timeout=TIME_RENDER_SOURCE_LIST)

    # Select the second source in the list to avoid marking unseen sources as seen
    source_item = list(gui.main_view.source_list.source_items.values())[1]
    source_widget = gui.main_view.source_list.itemWidget(source_item)
    qtbot.mouseClick(source_widget, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)

    def conversation_with_file_is_rendered():
        assert gui.main_view.view_layout.itemAt(0)
        conversation = gui.main_view.view_layout.itemAt(0).widget()
        assert isinstance(conversation, SourceConversationWrapper)
        file_widget = list(conversation.conversation_view.current_messages.values())[2]
        assert isinstance(file_widget, FileWidget)

    # Get the selected source conversation that contains a file attachment
    qtbot.waitUntil(conversation_with_file_is_rendered, timeout=TIME_RENDER_CONV_VIEW)
    conversation = gui.main_view.view_layout.itemAt(0).widget()
    file_widget = list(conversation.conversation_view.current_messages.values())[2]

    # If the file is not downloaded, click on the download button
    if file_widget.download_button.isVisible():
        qtbot.mouseClick(file_widget.download_button, Qt.LeftButton)
        qtbot.wait(TIME_CLICK_ACTION)
        qtbot.wait(TIME_FILE_DOWNLOAD)

    def check_for_export_wizard():
        assert file_widget.export_wizard

    assert file_widget.export_button.isVisible()
    # Begin exporting the file
    qtbot.mouseClick(file_widget.export_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.waitUntil(check_for_export_wizard, timeout=TIME_RENDER_EXPORT_WIZARD)

    return file_widget.export_wizard


@pytest.mark.vcr()
def test_export_wizard_device_locked(
    functional_test_logged_in_context, qtbot, mocker, mock_export_locked
):
    """
    Download a file, export it, and verify that the export is complete.

    Scenario:
        * No usb
        * Launch wizard
        * Insert USB
        * Passphrase prompt (successful)
        * Export success
    """
    export_wizard = _setup_export(
        functional_test_logged_in_context, qtbot, mocker, mock_export_locked
    )

    assert isinstance(
        export_wizard.currentPage(), PreflightPage
    ), f"Actual: {export_wizard.currentPage()} ({export_wizard.currentId()})"

    def check_insert_usb_page():
        assert isinstance(
            export_wizard.currentPage(), InsertUSBPage
        ), f"Actual: {export_wizard.currentPage()} ({export_wizard.currentId()})"

    # Move to "insert usb" screen
    qtbot.mouseClick(export_wizard.next_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.waitUntil(check_insert_usb_page, timeout=TIME_CLICK_ACTION)

    def check_password_page():
        assert isinstance(
            export_wizard.currentPage(), PassphraseWizardPage
        ), f"Actual: {export_wizard.currentPage()} ({export_wizard.currentId()})"

    # Continue exporting the file
    qtbot.mouseClick(export_wizard.next_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.waitUntil(check_password_page, timeout=TIME_CLICK_ACTION)

    # Continue exporting the file by entering a passphrase
    qtbot.mouseClick(export_wizard.currentPage().passphrase_field, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.keyClicks(export_wizard.currentPage().passphrase_field, "Passphrase Field")
    qtbot.mouseClick(export_wizard.next_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)

    assert isinstance(
        export_wizard.currentPage(), FinalPage
    ), f"Actual: {export_wizard.currentPage()} ({export_wizard.currentId()})"


@pytest.mark.vcr()
def test_export_wizard_dialog_device_already_unlocked(
    functional_test_logged_in_context, qtbot, mocker, mock_export_unlocked
):
    """
    Download a file, export it, and verify that the export is complete.

    Scenario:
        * Unlocked USB already inserted
        * Launch wizard, click "next"
        * Export success
    """
    export_wizard = _setup_export(
        functional_test_logged_in_context, qtbot, mocker, mock_export_unlocked
    )

    assert isinstance(
        export_wizard.currentPage(), PreflightPage
    ), f"Actual: {export_wizard.currentPage()} ({export_wizard.currentId()})"

    def check_insert_usb_page():
        assert isinstance(
            export_wizard.currentPage(), InsertUSBPage
        ), f"Actual: {export_wizard.currentPage()} ({export_wizard.currentId()})"

    # Move to "insert usb" screen
    qtbot.mouseClick(export_wizard.next_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.waitUntil(check_insert_usb_page, timeout=TIME_CLICK_ACTION)

    qtbot.mouseClick(export_wizard.next_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)

    # Click continue to export the file (skips password prompt screen)
    qtbot.mouseClick(export_wizard.next_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)

    assert isinstance(export_wizard.currentPage(), FinalPage)


@pytest.mark.vcr()
def test_export_wizard_no_device_then_bad_passphrase(
    functional_test_logged_in_context,
    qtbot,
    mocker,
    mock_export_no_usb_then_bad_passphrase,
):
    """
    Download a file, attempt export, encounter error that terminates the wizard early.

    Scenario:
        * No usb
        * Launch wizard
        * Insert USB
        * Enter passphrase incorrectly
        * Re-enter passphrase
        * Export succeeds
    """
    export_wizard = _setup_export(
        functional_test_logged_in_context,
        qtbot,
        mocker,
        mock_export_no_usb_then_bad_passphrase,
    )

    assert isinstance(
        export_wizard.currentPage(), PreflightPage
    ), f"Actual: {export_wizard.currentPage()} ({export_wizard.currentId()})"

    def check_insert_usb_page():
        assert isinstance(
            export_wizard.currentPage(), InsertUSBPage
        ), f"Actual: {export_wizard.currentPage()} ({export_wizard.currentId()})"

    # Move to "insert usb" screen
    qtbot.mouseClick(export_wizard.next_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.waitUntil(check_insert_usb_page, timeout=TIME_CLICK_ACTION)

    def check_password_page():
        assert isinstance(
            export_wizard.currentPage(), PassphraseWizardPage
        ), f"Actual: {export_wizard.currentPage()} ({export_wizard.currentId()})"

    # Move to password page
    qtbot.mouseClick(export_wizard.next_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.waitUntil(check_password_page, timeout=TIME_CLICK_ACTION)

    # (mis)type passphrase
    qtbot.mouseClick(export_wizard.currentPage().passphrase_field, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.keyClicks(export_wizard.currentPage().passphrase_field, "Oh no, I mistyped it!!")

    def check_password_page_with_error_details():
        """
        After an incorrect password, the 'error details' should be visible
        with a message about incorrect passphrase.
        """
        assert isinstance(
            export_wizard.currentPage(), PassphraseWizardPage
        ), f"Actual: {export_wizard.currentPage()} ({export_wizard.currentId()})"
        assert export_wizard.currentPage().error_details.isVisible()

    # Click next
    qtbot.mouseClick(export_wizard.next_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.waitUntil(check_password_page_with_error_details, timeout=TIME_CLICK_ACTION)

    # Retype passphrase
    qtbot.mouseClick(export_wizard.currentPage().passphrase_field, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.keyClicks(
        export_wizard.currentPage().passphrase_field, "correct passwords unlock swimmingly!"
    )

    def final_page():
        """
        After an incorrect password, the 'error details' should be visible
        with a message about incorrect passphrase.
        """
        assert isinstance(
            export_wizard.currentPage(), FinalPage
        ), f"Actual: {export_wizard.currentPage()} ({export_wizard.currentId()})"

    qtbot.mouseClick(export_wizard.next_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.waitUntil(final_page, timeout=TIME_CLICK_ACTION)

    assert isinstance(
        export_wizard.currentPage, FinalPage
    ), f"Actual: {export_wizard.currentPage()} ({export_wizard.currentId()})"


@pytest.mark.vcr()
def test_export_wizard_error(
    functional_test_logged_in_context, qtbot, mocker, mock_export_fail_early
):
    """
    Represents the following scenario:
        * Locked USB inserted
        * Export wizard launched
        * Unrecoverable error before export happens
          (eg, mount error)
    """
    export_wizard = _setup_export(
        functional_test_logged_in_context, qtbot, mocker, mock_export_fail_early
    )

    assert isinstance(
        export_wizard.currentPage(), PreflightPage
    ), f"Actual: {export_wizard.currentPage()} ({export_wizard.currentId()})"

    def check_password_page():
        assert isinstance(
            export_wizard.currentPage(), PassphraseWizardPage
        ), f"Actual: {export_wizard.currentPage()} ({export_wizard.currentId()})"

    # Move to "insert usb" screen
    qtbot.mouseClick(export_wizard.next_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.waitUntil(check_password_page, timeout=TIME_CLICK_ACTION)

    def check_error_page():
        assert isinstance(
            export_wizard.currentPage(), ErrorPage
        ), f"Actual: {export_wizard.currentPage()} ({export_wizard.currentId()})"

    # Continue exporting the file
    qtbot.mouseClick(export_wizard.next_button, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)

    assert isinstance(
        export_wizard.currentPage(), ErrorPage
    ), f"Actual: {export_wizard.currentPage()} ({export_wizard.currentId()})"
