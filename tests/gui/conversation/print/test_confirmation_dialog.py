import unittest
from unittest.mock import MagicMock

from PyQt5.QtTest import QSignalSpy

from securedrop_client import export
from securedrop_client.export import Printer, getPrinter
from securedrop_client.gui import conversation
from tests.helper import app  # noqa: F401

expected_message = {
    Printer.StatusUnknown: "Waiting for printer status to be known",
    Printer.StatusReady: "",
    Printer.StatusUnreachable: "Printer unreachable",
}


class TestConfirmationDialog(unittest.TestCase):
    def assertDialogReflectsPrinterStatus(
        self, dialog: conversation.PrintConfirmationDialog, status: Printer.Status
    ):
        self.assertTrue(
            expected_message[status] in dialog.text(),
            f'expected to find "{expected_message[status]}" in dialog text to reflect printer status {status}',  # noqa: E501
        )
        if status == Printer.StatusReady:
            self.assertTrue(
                self.dialog.continue_button.isEnabled(),
                f"expected print button to be enabled when status is {status}, was disabled",
            )
        else:
            self.assertTrue(
                not self.dialog.continue_button.isEnabled(),
                f"expected print button to be disabled when status is {status}, was enabled",
            )

    def setUp(self):
        printing_service = export.Service()
        file_name = "little_bird/conversation.txt"
        printer = getPrinter(printing_service)
        self.dialog = conversation.PrintConfirmationDialog(printer, file_name)
        self._printer = printer

    def test_assumes_printer_status_is_unknown_by_default(self):
        self.assertDialogReflectsPrinterStatus(self.dialog, Printer.StatusUnknown)

    @unittest.skip("WIP")
    def test_tracks_printer_status(self):
        for status in [Printer.StatusReady, Printer.StatusUnreachable, Printer.StatusUnknown]:
            self._printer.status = status
            self.assertDialogReflectsPrinterStatus(self.dialog, status)

    def test_emits_accepted_signal_when_accepted(self):
        dialog_accepted_emissions = QSignalSpy(self.dialog.accepted)
        self.assertTrue(dialog_accepted_emissions.isValid())

        self.dialog.accept()
        self.assertEqual(len(dialog_accepted_emissions), 1)

    def test_emits_rejected_signal_when_accepted(self):
        dialog_rejected_emissions = QSignalSpy(self.dialog.rejected)
        self.assertTrue(dialog_rejected_emissions.isValid())

        self.dialog.reject()
        self.assertEqual(len(dialog_rejected_emissions), 1)

    @unittest.skip("TODO: the dialog text should include its header's text")
    def test_displays_which_file_will_be_printed(self):
        file_name = "little_bird/conversation.txt"
        printer = MagicMock(spec=Printer)
        dialog = conversation.PrintConfirmationDialog(printer, file_name)
        self.assertTrue(
            file_name in dialog.text(), f'expected to find "{file_name}" in "{dialog.text()}"'
        )

    @unittest.skip("TODO: the dialog text should include its header's text")
    def test_displays_sanitized_file_name_not_dangerous_file_name(self):  # TODO: define "dangerous"
        dangerous_file_name = "FIXME dangerous"
        printer = MagicMock(spec=Printer)
        dialog = conversation.PrintConfirmationDialog(printer, dangerous_file_name)

        safe_file_name = "FIXME dangerous"
        self.assertTrue(
            safe_file_name in dialog.text(),
            f'expected to find "{safe_file_name}" in "{dialog.text()}"',
        )
        self.assertTrue(
            dangerous_file_name not in dialog.text(),
            f'expected NOT to find "{dangerous_file_name}" in "{dialog.text()}"',
        )
