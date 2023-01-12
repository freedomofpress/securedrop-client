import unittest
from unittest.mock import MagicMock, patch

from PyQt5.QtTest import QSignalSpy

from securedrop_client import export
from securedrop_client.export import ExportError, ExportStatus
from securedrop_client.export.cli import CLI
from securedrop_client.export.printer import clearPrinter
from securedrop_client.export.service import resetService
from securedrop_client.gui.conversation import PrintFileDialog
from tests.helper import app  # noqa: F401
from tests.helper import assertEmissions, emitsSignals, tearDownQtObjects


class TestPrintFileDialog(unittest.TestCase):
    def setUp(self):
        resetService()
        _export_service = export.getService()
        _export_service._cli = MagicMock(spec=CLI)
        _printer = export.getPrinter(_export_service)
        self.dialog = PrintFileDialog(
            _printer, file_location="file_location_fd3r4", file_name="file_name_lk4oi"
        )
        self._printer = _printer
        self._export_service = _export_service

    def tearDown(self):
        resetService()
        clearPrinter(self._export_service)
        tearDownQtObjects()

    def test_dialog_text_includes_header_and_body(self):
        default_header = "Preparing to print"
        default_body = "Managing printout risks"

        dialog_text = self.dialog.text()

        assert default_header in dialog_text, f'Expected "{default_header}" in "{dialog_text}"'
        assert default_body in dialog_text, f'Expected "{default_body}" in "{dialog_text}"'

    def test_continue_button_is_initially_diabled(self):
        assert (
            not self.dialog.continue_button.isEnabled()
        ), "Expected CONTINUE button to be disabled until the printer status is known, was enabled."  # noqa: E501

    @patch("securedrop_client.export.printer.Printer.status", export.Printer.StatusReady)
    def test_becomes_ready_to_print_when_printer_found(self):
        expected_text = "Ready to print"
        status_changed_emissions = QSignalSpy(self._printer.status_changed)
        assert status_changed_emissions.isValid()

        # Sanity check
        assert (
            expected_text not in self.dialog.text()
        ), f'Did not expect "{expected_text}" in "{self.dialog.text()}".'

        # Act.
        # There isn't anything to do beyond waiting for the status to be checked.
        assertEmissions(self, status_changed_emissions, 1)

        assert (
            expected_text in self.dialog.text()
        ), f'Expected "{expected_text}" in "{self.dialog.text()}".'
        assert (
            self.dialog.continue_button.isEnabled()
        ), "Expected CONTINUE button to be enabled when the printer was found, was disabled."

    @patch("securedrop_client.export.printer.Printer.status", export.Printer.StatusUnreachable)
    @patch(
        "securedrop_client.export.printer.Printer.last_error",
        ExportError(ExportStatus.PRINTER_NOT_FOUND),
    )
    def test_requests_printer_when_printer_not_found(self):
        printer_prompt = "Connect USB printer"
        status_changed_emissions = QSignalSpy(self._printer.status_changed)
        assert status_changed_emissions.isValid()

        # Sanity check
        assert (
            printer_prompt not in self.dialog.text()
        ), f'Did not expect "{printer_prompt}" in "{self.dialog.text()}".'

        # Act.
        emitsSignals(self._printer.status_changed.emit)
        assertEmissions(self, status_changed_emissions, 1)
        self.dialog.continue_button.click()  # Click "OK". This is how the dialog currently works.
        assertEmissions(self, status_changed_emissions, 2)

        assert (
            printer_prompt in self.dialog.text()
        ), f'Expected "{printer_prompt}" in "{self.dialog.text()}".'
        assert (
            self.dialog.continue_button.isEnabled()
        ), "Expected CONTINUE button to be enabled when the printer was not found, was disabled."

        # Subsequent printer status checks have the same effect
        #
        # The current implementation makes the dialog text depend
        # on the enablement of the button, which doesn't quite
        # make sense to me, but changing that is out of scope for now.
        emitsSignals(self._printer.status_changed.emit)
        assertEmissions(self, status_changed_emissions, 3)

        assert (
            printer_prompt in self.dialog.text()
        ), f'Expected "{printer_prompt}" in "{self.dialog.text()}".'
        assert (
            self.dialog.continue_button.isEnabled()
        ), "Expected CONTINUE button to be enabled when the printer was not found, was disabled."

    @patch("securedrop_client.export.printer.Printer.status", export.Printer.StatusUnreachable)
    @patch(
        "securedrop_client.export.printer.Printer.last_error",
        ExportError(ExportStatus.CALLED_PROCESS_ERROR),
    )
    def test_requests_printer_when_printer_otherwise_unreachable(self):

        expected_message = "See your administrator for help."
        status_changed_emissions = QSignalSpy(self._printer.status_changed)
        assert status_changed_emissions.isValid()

        # Sanity check
        assert (
            expected_message not in self.dialog.text()
        ), f'Did not expect "{expected_message}" in "{self.dialog.text()}".'

        # Act.
        emitsSignals(self._printer.status_changed.emit)
        assertEmissions(self, status_changed_emissions, 1)
        self.dialog.continue_button.click()  # Click "OK". This is how the dialog currently works.

        assert (
            expected_message in self.dialog.text()
        ), f'Expected "{expected_message}" in "{self.dialog.text()}".'
        assert (
            self.dialog.continue_button.isEnabled()
        ), "Expected CONTINUE button to be enabled when the printer is unreachable, was disabled."

    @patch("securedrop_client.export.printer.Printer.status", export.Printer.StatusUnreachable)
    @patch("securedrop_client.export.printer.Printer.last_error", None)
    def test_requests_printer_when_printer_unreachable_and_specific_error_is_missing(self):
        expected_message = "See your administrator for help."
        status_changed_emissions = QSignalSpy(self._printer.status_changed)
        assert status_changed_emissions.isValid()

        # Sanity check
        assert (
            expected_message not in self.dialog.text()
        ), f'Did not expect "{expected_message}" in "{self.dialog.text()}".'

        # Act.
        emitsSignals(self._printer.status_changed.emit)
        assertEmissions(self, status_changed_emissions, 1)
        self.dialog.continue_button.click()  # Click "OK". This is how the dialog currently works.
        assertEmissions(self, status_changed_emissions, 2)

        assert (
            expected_message in self.dialog.text()
        ), f'Expected "{expected_message}" in "{self.dialog.text()}".'
        assert (
            self.dialog.continue_button.isEnabled()
        ), "Expected CONTINUE button to be enabled when the printer is unreachable, was disabled."

        # Subsequent printer status checks have the same effect
        #
        # The current implementation makes the dialog text depend
        # on the enablement of the button, which doesn't quite
        # make sense to me, but changing that is out of scope for now.
        emitsSignals(self._printer.status_changed.emit)
        assertEmissions(self, status_changed_emissions, 3)

        assert (
            expected_message in self.dialog.text()
        ), f'Expected "{expected_message}" in "{self.dialog.text()}".'
        assert (
            self.dialog.continue_button.isEnabled()
        ), "Expected CONTINUE button to be enabled when the printer is unreachable, was disabled."


def test_PrintFileDialog_init(mocker):
    _show_starting_instructions_fn = mocker.patch(
        "securedrop_client.gui.conversation.PrintFileDialog._show_starting_instructions"
    )

    PrintFileDialog(mocker.MagicMock(), "mock_uuid", "mock.jpg")

    _show_starting_instructions_fn.assert_called_once_with()


def test_PrintFileDialog_init_sanitizes_filename(mocker):
    secure_qlabel = mocker.patch(
        "securedrop_client.gui.conversation.export.print_dialog.SecureQLabel"
    )
    filename = '<script>alert("boom!");</script>'

    PrintFileDialog(mocker.MagicMock(), "mock_uuid", filename)

    secure_qlabel.assert_any_call(filename, wordwrap=False, max_length=260)


def test_PrintFileDialog__show_starting_instructions(mocker, print_dialog):
    print_dialog._show_starting_instructions()

    # file123.jpg comes from the print_dialog fixture
    assert (
        print_dialog.header.text() == "Preparing to print:"
        "<br />"
        '<span style="font-weight:normal">file123.jpg</span>'
    )
    assert (
        print_dialog.body.text() == "<h2>Managing printout risks</h2>"
        "<b>QR codes and web addresses</b>"
        "<br />"
        "Never type in and open web addresses or scan QR codes contained in printed "
        "documents without taking security precautions. If you are unsure how to "
        "manage this risk, please contact your administrator."
        "<br /><br />"
        "<b>Printer dots</b>"
        "<br />"
        "Any part of a printed page may contain identifying information "
        "invisible to the naked eye, such as printer dots. Please carefully "
        "consider this risk when working with or publishing scanned printouts."
    )
    assert not print_dialog.header.isHidden()
    assert not print_dialog.header_line.isHidden()
    assert print_dialog.error_details.isHidden()
    assert not print_dialog.body.isHidden()
    assert not print_dialog.continue_button.isHidden()
    assert not print_dialog.cancel_button.isHidden()


def test_PrintFileDialog__show_insert_usb_message(mocker, print_dialog):
    print_dialog._show_insert_usb_message()

    assert print_dialog.header.text() == "Connect USB printer"
    assert print_dialog.body.text() == "Please connect your printer to a USB port."
    assert not print_dialog.header.isHidden()
    assert not print_dialog.header_line.isHidden()
    assert print_dialog.error_details.isHidden()
    assert not print_dialog.body.isHidden()
    assert not print_dialog.continue_button.isHidden()
    assert not print_dialog.cancel_button.isHidden()


def test_PrintFileDialog__show_generic_error_message(mocker, print_dialog):
    print_dialog.error_status = "mock_error_status"

    print_dialog._show_generic_error_message()

    assert print_dialog.header.text() == "Printing failed"
    assert print_dialog.body.text() == "mock_error_status: See your administrator for help."
    assert not print_dialog.header.isHidden()
    assert not print_dialog.header_line.isHidden()
    assert print_dialog.error_details.isHidden()
    assert not print_dialog.body.isHidden()
    assert not print_dialog.continue_button.isHidden()
    assert not print_dialog.cancel_button.isHidden()


def test_PrintFileDialog__print_file(mocker, print_dialog):
    print_dialog.close = mocker.MagicMock()

    print_dialog._print_file()

    print_dialog.close.assert_called_once_with()


def test_PrintFileDialog__on_print_preflight_check_succeeded(mocker, print_dialog):
    print_dialog._print_file = mocker.MagicMock()
    print_dialog.continue_button = mocker.MagicMock()
    print_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(print_dialog.continue_button, "isEnabled", return_value=False)

    print_dialog._on_print_preflight_check_succeeded()

    print_dialog._print_file.assert_not_called()
    print_dialog.continue_button.clicked.connect.assert_called_once_with(print_dialog._print_file)


def test_PrintFileDialog__on_print_preflight_check_succeeded_when_continue_enabled(
    mocker, print_dialog
):
    print_dialog._print_file = mocker.MagicMock()
    print_dialog.continue_button.setEnabled(True)

    print_dialog._on_print_preflight_check_succeeded()

    print_dialog._print_file.assert_called_once_with()


def test_PrintFileDialog__on_print_preflight_check_succeeded_enabled_after_preflight_success(
    mocker, print_dialog
):
    assert not print_dialog.continue_button.isEnabled()
    print_dialog._on_print_preflight_check_succeeded()
    assert print_dialog.continue_button.isEnabled()
