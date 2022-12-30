import unittest
from unittest.mock import patch

from PyQt5.QtTest import QSignalSpy

from securedrop_client import export
from securedrop_client.export.cli import CLI
from securedrop_client.export.cli import Error as CLIError


class TestExportServiceDiskInterface(unittest.TestCase):
    @patch(
        "securedrop_client.export.service.TemporaryDirectory.__enter__",
        return_value="tmpdir-48vj6",
    )
    @patch.object(CLI, "check_disk_encryption")
    @patch.object(CLI, "check_disk_presence")
    def test_uses_temporary_directory_for_disk_check(
        self, check_disk_presence, check_disk_encryption, temporary_directory
    ):
        export_service = export.getService()

        export_service.check_disk()

        check_disk_presence.assert_called_once_with("tmpdir-48vj6")
        check_disk_encryption.assert_called_once_with("tmpdir-48vj6")

    @patch.object(CLI, "check_disk_encryption")
    @patch.object(CLI, "check_disk_presence")
    def test_emits_luks_encrypted_disk_found_when_disk_check_succeeds(
        self, check_disk_presence, check_disk_encryption
    ):
        export_service = export.getService()
        luks_encrypted_disk_found_emissions = QSignalSpy(export_service.luks_encrypted_disk_found)
        luks_encrypted_disk_not_found_emissions = QSignalSpy(
            export_service.luks_encrypted_disk_not_found
        )
        assert luks_encrypted_disk_found_emissions.isValid()
        assert luks_encrypted_disk_not_found_emissions.isValid()

        export_service.check_disk()

        assert len(luks_encrypted_disk_found_emissions) == 1
        assert len(luks_encrypted_disk_not_found_emissions) == 0

    @patch.object(CLI, "check_disk_encryption")
    @patch.object(CLI, "check_disk_presence")
    def test_emits_luks_encrypted_disk_not_found_when_disk_is_not_present(
        self, check_disk_presence, check_disk_encryption
    ):
        check_error = CLIError(status="disk is missing")
        check_disk_presence.side_effect = check_error
        export_service = export.getService()
        luks_encrypted_disk_found_emissions = QSignalSpy(export_service.luks_encrypted_disk_found)
        luks_encrypted_disk_not_found_emissions = QSignalSpy(
            export_service.luks_encrypted_disk_not_found
        )
        assert luks_encrypted_disk_found_emissions.isValid()
        assert luks_encrypted_disk_not_found_emissions.isValid()

        export_service.check_disk()

        assert len(luks_encrypted_disk_found_emissions) == 0
        assert len(luks_encrypted_disk_not_found_emissions) == 1

    @patch.object(CLI, "check_disk_encryption")
    @patch.object(CLI, "check_disk_presence")
    def test_emits_luks_encrypted_disk_not_found_when_disk_is_not_luks_encrypted(
        self, check_disk_presence, check_disk_encryption
    ):
        check_error = CLIError(status="disk is not LUKS-encrypted")
        check_disk_encryption.side_effect = check_error
        export_service = export.getService()
        luks_encrypted_disk_found_emissions = QSignalSpy(export_service.luks_encrypted_disk_found)
        luks_encrypted_disk_not_found_emissions = QSignalSpy(
            export_service.luks_encrypted_disk_not_found
        )
        assert luks_encrypted_disk_found_emissions.isValid()
        assert luks_encrypted_disk_not_found_emissions.isValid()

        export_service.check_disk()

        assert len(luks_encrypted_disk_found_emissions) == 0
        assert len(luks_encrypted_disk_not_found_emissions) == 1

    @patch(
        "securedrop_client.export.service.TemporaryDirectory.__enter__",
        return_value="tmpdir-5b8wq",
    )
    @patch.object(CLI, "export")
    def test_uses_temporary_directory_for_exporting(self, cli_export, temporary_directory):
        valid_passphrase = "staple incorrect etcetera"
        valid_file_path = "file_path_328f42"
        expected_file_paths = [valid_file_path]
        export_service = export.getService()

        export_service.export([valid_file_path], valid_passphrase)

        cli_export.assert_called_once_with("tmpdir-5b8wq", expected_file_paths, valid_passphrase)

    @patch.object(CLI, "export")
    def test_emits_export_succeeded_and_export_finished_on_success(self, cli_export):
        export_service = export.getService()
        export_succeeded_emissions = QSignalSpy(export_service.export_succeeded)
        export_finished_emissions = QSignalSpy(export_service.export_finished)
        export_failed_emissions = QSignalSpy(export_service.export_failed)
        assert export_succeeded_emissions.isValid()
        assert export_finished_emissions.isValid()
        assert export_failed_emissions.isValid()

        valid_passphrase = "staple incorrect etcetera"
        valid_file_path = "file_path_328f42"
        expected_file_paths = [valid_file_path]

        export_service.export([valid_file_path], valid_passphrase)

        assert len(export_failed_emissions) == 0
        assert len(export_succeeded_emissions) == 1
        assert len(export_finished_emissions) == 1
        self.assertEqual(
            export_finished_emissions[0],
            [expected_file_paths],
            "Expected list of one exported file.",
        )

    @patch.object(CLI, "export")
    def test_emits_export_failed_and_export_finished_on_failure(self, cli_export):
        export_error = CLIError(status="some error happened")
        cli_export.side_effect = export_error
        export_service = export.getService()
        export_failed_emissions = QSignalSpy(export_service.export_failed)
        export_finished_emissions = QSignalSpy(export_service.export_finished)
        export_succeeded_emissions = QSignalSpy(export_service.export_succeeded)
        assert export_failed_emissions.isValid()
        assert export_finished_emissions.isValid()
        assert export_succeeded_emissions.isValid()

        valid_passphrase = "staple incorrect etcetera"
        valid_file_path = "file_path_243f4f"
        expected_file_paths = [valid_file_path]

        export_service.export([valid_file_path], valid_passphrase)

        assert len(export_succeeded_emissions) == 0
        assert len(export_failed_emissions) == 1
        assert len(export_finished_emissions) == 1
        self.assertEqual(
            export_failed_emissions[0],
            [export_error],
            "Expected error object ot be emitted on failure.",
        )
        self.assertEqual(
            export_finished_emissions[0],
            [expected_file_paths],
            "Expected list of one exported file.",
        )


class TestExportServicePrinterInterface(unittest.TestCase):
    @patch(
        "securedrop_client.export.service.TemporaryDirectory.__enter__",
        return_value="tmpdir-sq324f",
    )
    @patch.object(CLI, "check_printer_status")
    def test_uses_temporary_directory_for_printer_status_check(
        self, check_printer_status, temporary_directory
    ):
        export_service = export.getService()

        export_service.check_printer_status()

        check_printer_status.assert_called_once_with("tmpdir-sq324f")

    @patch.object(CLI, "check_printer_status")
    def test_emits_printer_found_ready_when_printer_status_check_succeeds(
        self, check_printer_status
    ):
        export_service = export.getService()
        printer_found_ready_emissions = QSignalSpy(export_service.printer_found_ready)
        assert printer_found_ready_emissions.isValid()

        export_service.check_printer_status()

        assert len(printer_found_ready_emissions) == 1
        assert printer_found_ready_emissions[0] == []

    @patch.object(CLI, "check_printer_status")
    def test_emits_printer_not_found_ready_when_printer_status_check_fails(
        self, check_printer_status
    ):
        expected_error = export.ExportError("bang!")
        check_printer_status.side_effect = expected_error
        export_service = export.getService()
        printer_not_found_ready_emissions = QSignalSpy(export_service.printer_not_found_ready)
        assert printer_not_found_ready_emissions.isValid()

        export_service.check_printer_status()

        assert len(printer_not_found_ready_emissions) == 1
        assert printer_not_found_ready_emissions[0] == [expected_error]

    @patch(
        "securedrop_client.export.service.TemporaryDirectory.__enter__",
        return_value="tmpdir-94jf3",
    )
    @patch.object(CLI, "print")
    def test_uses_temporary_directory_for_printing(self, print, temporary_directory):
        valid_file_path = "file_path_328f42"
        expected_file_paths = [valid_file_path]
        export_service = export.getService()

        export_service.print([valid_file_path])

        print.assert_called_once_with("tmpdir-94jf3", expected_file_paths)

    @patch.object(CLI, "print")
    def test_emits_print_succeeded_and_print_finished_on_success(self, print):
        export_service = export.getService()
        print_succeeded_emissions = QSignalSpy(export_service.print_succeeded)
        print_finished_emissions = QSignalSpy(export_service.print_finished)
        print_failed_emissions = QSignalSpy(export_service.print_failed)
        assert print_succeeded_emissions.isValid()
        assert print_finished_emissions.isValid()
        assert print_failed_emissions.isValid()

        valid_file_path = "file_path_328f42"
        expected_file_paths = [valid_file_path]

        export_service.print([valid_file_path])

        assert len(print_failed_emissions) == 0
        assert len(print_succeeded_emissions) == 1
        assert len(print_finished_emissions) == 1
        self.assertEqual(
            print_finished_emissions[0], [expected_file_paths], "Expected list of one printed file."
        )

    @patch.object(CLI, "print")
    def test_emits_print_failed_and_print_finished_on_failure(self, print):
        print_error = CLIError(status="some error happened")
        print.side_effect = print_error
        export_service = export.getService()
        print_failed_emissions = QSignalSpy(export_service.print_failed)
        print_finished_emissions = QSignalSpy(export_service.print_finished)
        print_succeeded_emissions = QSignalSpy(export_service.print_succeeded)
        assert print_failed_emissions.isValid()
        assert print_finished_emissions.isValid()
        assert print_succeeded_emissions.isValid()

        valid_file_path = "file_path_243f4f"
        expected_file_paths = [valid_file_path]

        export_service.print([valid_file_path])

        assert len(print_succeeded_emissions) == 0
        assert len(print_failed_emissions) == 1
        assert len(print_finished_emissions) == 1
        self.assertEqual(
            print_failed_emissions[0],
            [print_error],
            "Expected error object ot be emitted on failure.",
        )
        self.assertEqual(
            print_finished_emissions[0], [expected_file_paths], "Expected list of one printed file."
        )
