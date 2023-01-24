import unittest
from unittest.mock import MagicMock, patch

from PyQt5.QtTest import QSignalSpy

from securedrop_client import export
from securedrop_client.export import ExportError, ExportStatus, getDisk
from securedrop_client.export.cli import CLI
from securedrop_client.export.disk import clearDisk
from securedrop_client.export.service import resetService
from securedrop_client.gui.conversation import ExportFileDialog
from tests.helper import app  # noqa: F401
from tests.helper import assertEmissions, emitsSignals, tearDownQtObjects


class TestExportFileDialog(unittest.TestCase):
    def setUp(self):
        resetService()
        _export_service = export.getService()
        _export_service._cli = MagicMock(spec=CLI)
        _disk = export.getDisk(_export_service)
        self.dialog = ExportFileDialog(
            _disk, file_location="file_location_fd3r4", file_name="file_name_lk4oi"
        )
        self._disk = _disk
        self._export_service = _export_service

    def tearDown(self):
        resetService()
        clearDisk(self._export_service)
        tearDownQtObjects()
        pass

    def test_dialog_text_includes_header_and_body(self):
        # There is a race condition when initializing the dialog,
        # that's why it is created after disabling the service check_disk.
        # If the service responds quick enough, the successful disk check
        # causes the dialog header to be updated.
        # self._export_service.check_disk = MagicMock()
        # Or not?
        self.dialog = ExportFileDialog(
            self._disk, file_location="file_location_fd3r4", file_name="file_name_lk4oi"
        )

        default_header = "Preparing to export"
        default_body = "Understand the risks before exporting files"

        dialog_text = self.dialog.text()

        self.assertTrue(
            default_header in dialog_text, f'Expected "{default_header}" in "{dialog_text}"'
        )
        self.assertTrue(
            default_body in dialog_text, f'Expected "{default_body}" in "{dialog_text}"'
        )

    @patch("securedrop_client.export.disk.Disk.status", export.Disk.StatusReachable)
    def test_requests_disk_passphrase_when_LUKS_encrypted_disk_found(self):
        passphrase_prompt = "Enter passphrase for USB drive"
        status_changed_emissions = QSignalSpy(self._disk.status_changed)
        assert status_changed_emissions.isValid()

        # Sanity check
        self.assertFalse(
            passphrase_prompt in self.dialog.text(),
            f'Did not expect "{passphrase_prompt}" in "{self.dialog.text()}".',
        )

        # Act.
        emitsSignals(self._disk.status_changed.emit)
        assertEmissions(self, status_changed_emissions, 1)
        self.dialog.continue_button.click()  # Click "OK". This is how the dialog currently works.

        self.assertTrue(
            passphrase_prompt in self.dialog.text(),
            f'Expected "{passphrase_prompt}" in "{self.dialog.text()}".',
        )

    @patch("securedrop_client.export.disk.Disk.status", export.Disk.StatusUnreachable)
    @patch(
        "securedrop_client.export.disk.Disk.last_error", ExportError(ExportStatus.USB_NOT_CONNECTED)
    )
    def test_prompts_for_disk_when_disk_unreachable(self):
        expected_message = "Please insert one of the export drives"
        status_changed_emissions = QSignalSpy(self._disk.status_changed)
        assert status_changed_emissions.isValid()

        # Sanity check
        self.assertFalse(
            expected_message in self.dialog.text(),
            f'Did not expect "{expected_message}" in "{self.dialog.text()}".',
        )

        # Act.
        emitsSignals(self._disk.status_changed.emit)
        assertEmissions(self, status_changed_emissions, 1)
        self.dialog.continue_button.click()  # Click "OK". This is how the dialog currently works.

        self.assertTrue(
            expected_message in self.dialog.text(),
            f'Expected "{expected_message}" in "{self.dialog.text()}".',
        )

    @patch("securedrop_client.export.disk.Disk.status", export.Disk.StatusUnreachable)
    @patch("securedrop_client.export.disk.Disk.last_error", None)
    def test_displays_generic_error_message_when_disk_unreachanble_and_specific_error_is_missing(
        self,
    ):
        expected_message = "See your administrator for help."
        status_changed_emissions = QSignalSpy(self._disk.status_changed)
        assert status_changed_emissions.isValid()

        # Sanity check
        self.assertFalse(
            expected_message in self.dialog.text(),
            f'Did not expect "{expected_message}" in "{self.dialog.text()}".',
        )

        # Act.
        emitsSignals(self._disk.status_changed.emit)
        assertEmissions(self, status_changed_emissions, 1)
        self.dialog.continue_button.click()  # Click "OK". This is how the dialog currently works.

        self.assertTrue(
            expected_message in self.dialog.text(),
            f'Expected "{expected_message}" in "{self.dialog.text()}".',
        )

    @patch("securedrop_client.export.disk.Disk.last_error", None)
    def test_displays_generic_error_message_when_export_fails_and_specific_error_is_missing(
        self,
    ):
        expected_message = "See your administrator for help."
        export_failed_emissions = QSignalSpy(self._disk.export_failed)
        assert export_failed_emissions.isValid()

        # This doesn't quite make sense to me, but thats's how the dialog
        # currently works. It is the state of the button that determines
        # whether error messages are displayed immediately.
        self.dialog.continue_button.setEnabled(True)

        # Sanity check
        self.assertFalse(
            expected_message in self.dialog.text(),
            f'Did not expect "{expected_message}" in "{self.dialog.text()}".',
        )

        # Act.
        emitsSignals(self._disk.export_failed.emit)
        assertEmissions(self, export_failed_emissions, 1)
        self.dialog.continue_button.click()  # Click "OK". This is how the dialog currently works.

        self.assertTrue(
            expected_message in self.dialog.text(),
            f'Expected "{expected_message}" in "{self.dialog.text()}".',
        )


def test_ExportDialog_init(mocker):
    _show_starting_instructions_fn = mocker.patch(
        "securedrop_client.gui.conversation.ExportFileDialog._show_starting_instructions"
    )

    export_dialog = ExportFileDialog(mocker.MagicMock(), "mock_uuid", "mock.jpg")

    _show_starting_instructions_fn.assert_called_once_with()
    assert export_dialog.passphrase_form.isHidden()


def test_ExportDialog_init_sanitizes_filename(mocker):
    secure_qlabel = mocker.patch("securedrop_client.gui.conversation.export.dialog.SecureQLabel")
    mocker.patch("securedrop_client.gui.widgets.QVBoxLayout.addWidget")
    filename = '<script>alert("boom!");</script>'

    ExportFileDialog(mocker.MagicMock(), "mock_uuid", filename)

    secure_qlabel.assert_any_call(filename, wordwrap=False, max_length=260)


def test_ExportDialog__show_starting_instructions(mocker, export_dialog):
    export_dialog._show_starting_instructions()

    # file123.jpg comes from the export_dialog fixture
    assert (
        export_dialog.header.text() == "Preparing to export:"
        "<br />"
        '<span style="font-weight:normal">file123.jpg</span>'
    )
    assert (
        export_dialog.body.text() == "<h2>Understand the risks before exporting files</h2>"
        "<b>Malware</b>"
        "<br />"
        "This workstation lets you open files securely. If you open files on another "
        "computer, any embedded malware may spread to your computer or network. If you are "
        "unsure how to manage this risk, please print the file, or contact your "
        "administrator."
        "<br /><br />"
        "<b>Anonymity</b>"
        "<br />"
        "Files submitted by sources may contain information or hidden metadata that "
        "identifies who they are. To protect your sources, please consider redacting files "
        "before working with them on network-connected computers."
    )
    assert not export_dialog.header.isHidden()
    assert not export_dialog.header_line.isHidden()
    assert export_dialog.error_details.isHidden()
    assert not export_dialog.body.isHidden()
    assert export_dialog.passphrase_form.isHidden()
    assert not export_dialog.continue_button.isHidden()
    assert not export_dialog.cancel_button.isHidden()


def test_ExportDialog___show_passphrase_request_message(mocker, export_dialog):
    export_dialog._show_passphrase_request_message()

    assert export_dialog.header.text() == "Enter passphrase for USB drive"
    assert not export_dialog.header.isHidden()
    assert export_dialog.header_line.isHidden()
    assert export_dialog.error_details.isHidden()
    assert export_dialog.body.isHidden()
    assert not export_dialog.passphrase_form.isHidden()
    assert not export_dialog.continue_button.isHidden()
    assert not export_dialog.cancel_button.isHidden()


def test_ExportDialog__show_passphrase_request_message_again(mocker, export_dialog):
    export_dialog._show_passphrase_request_message_again()

    assert export_dialog.header.text() == "Enter passphrase for USB drive"
    assert (
        export_dialog.error_details.text()
        == "The passphrase provided did not work. Please try again."
    )
    assert export_dialog.body.isHidden()
    assert not export_dialog.header.isHidden()
    assert export_dialog.header_line.isHidden()
    assert not export_dialog.error_details.isHidden()
    assert export_dialog.body.isHidden()
    assert not export_dialog.passphrase_form.isHidden()
    assert not export_dialog.continue_button.isHidden()
    assert not export_dialog.cancel_button.isHidden()


def test_ExportDialog__show_success_message(mocker, export_dialog):
    export_dialog._show_success_message()

    assert export_dialog.header.text() == "Export successful"
    assert (
        export_dialog.body.text()
        == "Remember to be careful when working with files outside of your Workstation machine."
    )
    assert not export_dialog.header.isHidden()
    assert not export_dialog.header_line.isHidden()
    assert export_dialog.error_details.isHidden()
    assert not export_dialog.body.isHidden()
    assert export_dialog.passphrase_form.isHidden()
    assert not export_dialog.continue_button.isHidden()
    assert export_dialog.cancel_button.isHidden()


def test_ExportDialog__show_insert_usb_message(mocker, export_dialog):
    export_dialog._show_insert_usb_message()

    assert export_dialog.header.text() == "Insert encrypted USB drive"
    assert (
        export_dialog.body.text()
        == "Please insert one of the export drives provisioned specifically "
        "for the SecureDrop Workstation."
    )
    assert not export_dialog.header.isHidden()
    assert not export_dialog.header_line.isHidden()
    assert export_dialog.error_details.isHidden()
    assert not export_dialog.body.isHidden()
    assert export_dialog.passphrase_form.isHidden()
    assert not export_dialog.continue_button.isHidden()
    assert not export_dialog.cancel_button.isHidden()


def test_ExportDialog__show_insert_encrypted_usb_message(mocker, export_dialog):
    export_dialog._show_insert_encrypted_usb_message()

    assert export_dialog.header.text() == "Insert encrypted USB drive"
    assert (
        export_dialog.error_details.text()
        == "Either the drive is not encrypted or there is something else wrong with it."
    )
    assert (
        export_dialog.body.text()
        == "Please insert one of the export drives provisioned specifically for the SecureDrop "
        "Workstation."
    )
    assert not export_dialog.header.isHidden()
    assert not export_dialog.header_line.isHidden()
    assert not export_dialog.error_details.isHidden()
    assert not export_dialog.body.isHidden()
    assert export_dialog.passphrase_form.isHidden()
    assert not export_dialog.continue_button.isHidden()
    assert not export_dialog.cancel_button.isHidden()


def test_ExportDialog__show_generic_error_message(mocker, export_dialog):
    export_dialog.error_status = "mock_error_status"

    export_dialog._show_generic_error_message()

    assert export_dialog.header.text() == "Export failed"
    assert export_dialog.body.text() == "mock_error_status: See your administrator for help."
    assert not export_dialog.header.isHidden()
    assert not export_dialog.header_line.isHidden()
    assert export_dialog.error_details.isHidden()
    assert not export_dialog.body.isHidden()
    assert export_dialog.passphrase_form.isHidden()
    assert not export_dialog.continue_button.isHidden()
    assert not export_dialog.cancel_button.isHidden()


def test_ExportDialog__export_file(mocker, export_dialog, export_service):
    # Remember the export disk is a singleton,
    # so this actually modifies the disk associated
    # with the dialog.
    disk = getDisk(export_service)
    file_export_requested_emissions = QSignalSpy(export_dialog.file_export_requested)
    export_done_emissions = QSignalSpy(disk.export_done)
    assert file_export_requested_emissions.isValid()
    assert export_done_emissions.isValid()

    export_dialog.passphrase_field.text = mocker.MagicMock(return_value="mock_passphrase")

    export_dialog._export_file()

    file_export_requested_emissions.wait(50)
    export_done_emissions.wait(50)

    assert len(file_export_requested_emissions) == 1
    assert file_export_requested_emissions[0] == [[export_dialog.file_location], "mock_passphrase"]

    assert len(export_done_emissions) == 1


def test_ExportDialog__on_export_preflight_check_succeeded(mocker, export_dialog):
    export_dialog._show_passphrase_request_message = mocker.MagicMock()
    export_dialog.continue_button = mocker.MagicMock()
    export_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(export_dialog.continue_button, "isEnabled", return_value=False)

    export_dialog._on_export_preflight_check_succeeded()

    export_dialog._show_passphrase_request_message.assert_not_called()
    export_dialog.continue_button.clicked.connect.assert_called_once_with(
        export_dialog._show_passphrase_request_message
    )


def test_ExportDialog__on_export_preflight_check_succeeded_when_continue_enabled(
    mocker, export_dialog
):
    export_dialog._show_passphrase_request_message = mocker.MagicMock()
    export_dialog.continue_button.setEnabled(True)

    export_dialog._on_export_preflight_check_succeeded()

    export_dialog._show_passphrase_request_message.assert_called_once_with()


def test_ExportDialog__on_export_preflight_check_succeeded_enabled_after_preflight_success(
    mocker, export_dialog
):
    assert not export_dialog.continue_button.isEnabled()
    export_dialog._on_export_preflight_check_succeeded()
    assert export_dialog.continue_button.isEnabled()


def test_ExportDialog__on_export_preflight_check_succeeded_enabled_after_preflight_failure(
    mocker, export_dialog
):
    assert not export_dialog.continue_button.isEnabled()
    export_dialog._on_export_preflight_check_failed()
    assert export_dialog.continue_button.isEnabled()


# FIXME This test mocks the object under test.
# FIXME This test asserts on an implementaiton detail, not on behavior.
def test_ExportDialog__on_export_preflight_check_failed(mocker, export_dialog, export_service):
    # Remember the export disk is a singleton,
    # so this actually modifies the disk associated
    # with the dialog.
    disk = getDisk(export_service)
    disk._last_error = ExportError("mock_error_status")
    export_dialog._update_dialog = mocker.MagicMock()

    export_dialog._on_export_preflight_check_failed()

    export_dialog._update_dialog.assert_called_with("mock_error_status")


def test_ExportDialog__on_export_succeeded(mocker, export_dialog):
    export_dialog._show_success_message = mocker.MagicMock()

    export_dialog._on_export_succeeded()

    export_dialog._show_success_message.assert_called_once_with()


# FIXME This test mocks the object under test.
# FIXME This test asserts on an implementaiton detail, not on behavior.
def test_ExportDialog__on_export_failed(mocker, export_dialog, export_service):
    # Remember the export disk is a singleton,
    # so this actually modifies the disk associated
    # with the dialog.
    disk = getDisk(export_service)
    disk._last_error = ExportError("mock_error_status")
    export_dialog._update_dialog = mocker.MagicMock()

    export_dialog._on_export_failed()

    export_dialog._update_dialog.assert_called_with("mock_error_status")


def test_ExportDialog__update_dialog_when_status_is_USB_NOT_CONNECTED(mocker, export_dialog):
    export_dialog._show_insert_usb_message = mocker.MagicMock()
    export_dialog.continue_button = mocker.MagicMock()
    export_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(export_dialog.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    export_dialog._update_dialog(ExportStatus.USB_NOT_CONNECTED)
    export_dialog.continue_button.clicked.connect.assert_called_once_with(
        export_dialog._show_insert_usb_message
    )

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(export_dialog.continue_button, "isEnabled", return_value=True)
    export_dialog._update_dialog(ExportStatus.USB_NOT_CONNECTED)
    export_dialog._show_insert_usb_message.assert_called_once_with()


def test_ExportDialog__update_dialog_when_status_is_BAD_PASSPHRASE(mocker, export_dialog):
    export_dialog._show_passphrase_request_message_again = mocker.MagicMock()
    export_dialog.continue_button = mocker.MagicMock()
    export_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(export_dialog.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    export_dialog._update_dialog(ExportStatus.BAD_PASSPHRASE)
    export_dialog.continue_button.clicked.connect.assert_called_once_with(
        export_dialog._show_passphrase_request_message_again
    )

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(export_dialog.continue_button, "isEnabled", return_value=True)
    export_dialog._update_dialog(ExportStatus.BAD_PASSPHRASE)
    export_dialog._show_passphrase_request_message_again.assert_called_once_with()


def test_ExportDialog__update_dialog_when_status_DISK_ENCRYPTION_NOT_SUPPORTED_ERROR(
    mocker, export_dialog
):
    export_dialog._show_insert_encrypted_usb_message = mocker.MagicMock()
    export_dialog.continue_button = mocker.MagicMock()
    export_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(export_dialog.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    export_dialog._update_dialog(ExportStatus.DISK_ENCRYPTION_NOT_SUPPORTED_ERROR)
    export_dialog.continue_button.clicked.connect.assert_called_once_with(
        export_dialog._show_insert_encrypted_usb_message
    )

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(export_dialog.continue_button, "isEnabled", return_value=True)
    export_dialog._update_dialog(ExportStatus.DISK_ENCRYPTION_NOT_SUPPORTED_ERROR)
    export_dialog._show_insert_encrypted_usb_message.assert_called_once_with()


def test_ExportDialog__update_dialog_when_status_is_CALLED_PROCESS_ERROR(mocker, export_dialog):
    export_dialog._show_generic_error_message = mocker.MagicMock()
    export_dialog.continue_button = mocker.MagicMock()
    export_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(export_dialog.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    export_dialog._update_dialog(ExportStatus.CALLED_PROCESS_ERROR)
    export_dialog.continue_button.clicked.connect.assert_called_once_with(
        export_dialog._show_generic_error_message
    )
    assert export_dialog.error_status == ExportStatus.CALLED_PROCESS_ERROR

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(export_dialog.continue_button, "isEnabled", return_value=True)
    export_dialog._update_dialog(ExportStatus.CALLED_PROCESS_ERROR)
    export_dialog._show_generic_error_message.assert_called_once_with()
    assert export_dialog.error_status == ExportStatus.CALLED_PROCESS_ERROR


def test_ExportDialog__update_dialog_when_status_is_unknown(mocker, export_dialog):
    export_dialog._show_generic_error_message = mocker.MagicMock()
    export_dialog.continue_button = mocker.MagicMock()
    export_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(export_dialog.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    export_dialog._update_dialog("Some Unknown Error Status")
    export_dialog.continue_button.clicked.connect.assert_called_once_with(
        export_dialog._show_generic_error_message
    )
    assert export_dialog.error_status == "Some Unknown Error Status"

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(export_dialog.continue_button, "isEnabled", return_value=True)
    export_dialog._update_dialog("Some Unknown Error Status")
    export_dialog._show_generic_error_message.assert_called_once_with()
    assert export_dialog.error_status == "Some Unknown Error Status"
