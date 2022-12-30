import unittest
from unittest.mock import patch

import pytest

from securedrop_client import export
from securedrop_client.export.archive import Archive
from securedrop_client.export.cli import CLI, Status


class TestExportServiceCLIInterfaceForDisk(unittest.TestCase):
    SUCCESS_STATUS = ""  # sd-devices API
    not_SUCCESS_STATUS = "whatever"
    not_USB_CONNECTED = "whatever"
    not_DISK_ENCRYPTED = "whatever"

    @patch.object(CLI, "_export_archive", return_value=SUCCESS_STATUS)
    @patch.object(Archive, "create_archive")
    def test_disk_presence_check_returns_without_errors_when_empty_response(
        self, create_archive, export_archive
    ):
        export_service = export.getService()
        valid_archive_path = "archive_path_0fh437"

        export_service._cli.check_disk_presence(valid_archive_path)

        assert True  # no exception was raised

    @patch.object(CLI, "_export_archive", return_value=Status.USB_CONNECTED)
    @patch.object(Archive, "create_archive")
    def test_disk_presence_check_returns_without_errors_when_response_is_USB_CONNECTED(
        self, create_archive, export_archive
    ):
        export_service = export.getService()
        valid_archive_path = "archive_path_0fh437"

        export_service._cli.check_disk_presence(valid_archive_path)

        assert True  # no exception was raised

    @patch.object(CLI, "_export_archive", return_value=Status.USB_CONNECTED)
    @patch.object(Archive, "create_archive", return_value="archive_path_03234t")
    def test_disk_presence_check_exports_a_specifically_created_archive(
        self, create_archive, export_archive
    ):
        expected_archive_path = "archive_path_03234t"
        expected_archive_dir = "archive_dir_ly4421"
        export_service = export.getService()

        export_service._cli.check_disk_presence(expected_archive_dir)

        export_archive.assert_called_once_with(expected_archive_path)
        create_archive.assert_called_once_with(
            expected_archive_dir, "usb-test.sd-export", {"device": "usb-test"}
        )

    @patch.object(CLI, "_export_archive", return_value=not_USB_CONNECTED)
    @patch.object(Archive, "create_archive")
    def test_disk_presence_check_raises_export_error_when_response_not_empty_or_USB_CONNECTED(
        self, create_archive, export_archive
    ):
        valid_archive_path = "archive_path_1dsd63"
        export_service = export.getService()

        with pytest.raises(export.ExportError):
            export_service._cli.check_disk_presence(valid_archive_path)

    @patch.object(CLI, "_export_archive", return_value=SUCCESS_STATUS)
    @patch.object(Archive, "create_archive")
    def test_disk_encryption_check_returns_without_errors_when_empty_response(
        self, create_archive, export_archive
    ):
        export_service = export.getService()
        valid_archive_path = "archive_path_0kdy3"

        export_service._cli.check_disk_encryption(valid_archive_path)

        assert True  # no exception was raised

    @patch.object(CLI, "_export_archive", return_value=Status.DISK_ENCRYPTED)
    @patch.object(Archive, "create_archive")
    def test_disk_encryption_check_returns_without_errors_when_response_is_DISK_ENCRYPTED(
        self, create_archive, export_archive
    ):
        export_service = export.getService()
        valid_archive_path = "archive_path_0kdy3"

        export_service._cli.check_disk_encryption(valid_archive_path)

        assert True  # no exception was raised

    @patch.object(CLI, "_export_archive", return_value=Status.DISK_ENCRYPTED)
    @patch.object(Archive, "create_archive", return_value="archive_path_243kjg")
    def test_disk_encryption_check_exports_a_specifically_created_archive(
        self, create_archive, export_archive
    ):
        expected_archive_path = "archive_path_243kjg"
        expected_archive_dir = "archive_dir_zsoeq"
        export_service = export.getService()

        export_service._cli.check_disk_encryption(expected_archive_dir)

        export_archive.assert_called_once_with(expected_archive_path)
        create_archive.assert_called_once_with(
            expected_archive_dir, "disk-test.sd-export", {"device": "disk-test"}
        )

    @patch.object(CLI, "_export_archive", return_value=not_DISK_ENCRYPTED)
    @patch.object(Archive, "create_archive")
    def test_disk_encryption_check_raises_export_error_when_response_not_empty_or_DISK_EMCRYPTED(
        self, create_archive, export_archive
    ):
        valid_archive_path = "archive_path_034d3"
        export_service = export.getService()

        with pytest.raises(export.ExportError):
            export_service._cli.check_disk_encryption(valid_archive_path)

    @patch.object(CLI, "_export_archive", return_value=SUCCESS_STATUS)
    @patch.object(Archive, "create_archive")
    def test_export_returns_without_errors_when_empty_response(
        self, create_archive, export_archive
    ):
        export_service = export.getService()
        valid_archive_dir = "archive_dir_sfutqe"
        valid_file_path = "memo.txt"
        valid_passphrase = "battery horse etcetera"

        export_service._cli.export(valid_archive_dir, [valid_file_path], valid_passphrase)

        assert True  # no exception was raised

    @patch.object(CLI, "_export_archive", return_value=SUCCESS_STATUS)
    @patch.object(Archive, "create_archive", return_value="archive_path_3sa47")
    def test_export_exports_a_specifically_created_archive(self, create_archive, export_archive):
        expected_file_path = "memo-df434.txt"
        expected_archive_path = "archive_path_3sa47"
        expected_archive_dir = "archive_dir_3209n4"
        valid_passphrase = "battery horse etcetera"
        export_service = export.getService()

        export_service._cli.export(expected_archive_dir, [expected_file_path], valid_passphrase)

        export_archive.assert_called_once_with(expected_archive_path)
        create_archive.assert_called_once_with(
            expected_archive_dir,
            "archive.sd-export",
            {
                "device": "disk",
                "encryption_method": "luks",
                "encryption_key": "battery horse etcetera",
            },
            [expected_file_path],
        )

    @patch.object(CLI, "_export_archive", return_value=not_SUCCESS_STATUS)
    @patch.object(Archive, "create_archive")
    def test_export_raises_export_error_when_response_not_empty(
        self, create_archive, export_archive
    ):
        valid_archive_dir = "archive_dir_elriu3"
        valid_file_path = "memo.txt"
        valid_passphrase = "battery horse etcetera"
        export_service = export.getService()

        with pytest.raises(export.ExportError):
            export_service._cli.export(valid_archive_dir, [valid_file_path], valid_passphrase)


class TestExportServiceCLIInterfaceForPrinter(unittest.TestCase):
    SUCCESS_STATUS = ""  # sd-devices API
    not_SUCCESS_STATUS = "whatever"

    @patch.object(CLI, "_export_archive", return_value=SUCCESS_STATUS)
    @patch.object(Archive, "create_archive")
    def test_printer_status_check_returns_without_errors_when_empty_response(
        self, create_archive, export_archive
    ):
        export_service = export.getService()
        valid_archive_path = "archive_path_13kn3"

        export_service._cli.check_printer_status(valid_archive_path)

        assert True  # no exception was raised

    @patch.object(CLI, "_export_archive", return_value=SUCCESS_STATUS)
    @patch.object(Archive, "create_archive", return_value="archive_path_9f483f")
    def test_printer_status_check_exports_a_specifically_created_archive(
        self, create_archive, export_archive
    ):
        expected_archive_path = "archive_path_9f483f"
        expected_archive_dir = "archive_dir_2i19c"
        export_service = export.getService()

        export_service._cli.check_printer_status(expected_archive_dir)

        export_archive.assert_called_once_with(expected_archive_path)
        create_archive.assert_called_once_with(
            expected_archive_dir, "printer-preflight.sd-export", {"device": "printer-preflight"}
        )

    @patch.object(CLI, "_export_archive", return_value=not_SUCCESS_STATUS)
    @patch.object(Archive, "create_archive")
    def test_printer_status_check_raises_export_error_when_response_not_empty(
        self, create_archive, export_archive
    ):
        valid_archive_path = "archive_path_034d3"
        export_service = export.getService()

        with pytest.raises(export.ExportError):
            export_service._cli.check_printer_status(valid_archive_path)

    @patch.object(CLI, "_export_archive", return_value=SUCCESS_STATUS)
    @patch.object(Archive, "create_archive")
    def test_print_returns_without_errors_when_empty_response(self, create_archive, export_archive):
        export_service = export.getService()
        valid_archive_dir = "archive_dir_84jde"
        valid_file_path = "memo.txt"

        export_service._cli.print(valid_archive_dir, [valid_file_path])

        assert True  # no exception was raised

    @patch.object(CLI, "_export_archive", return_value=SUCCESS_STATUS)
    @patch.object(Archive, "create_archive", return_value="archive_path_2jr723")
    def test_print_exports_a_specifically_created_archive(self, create_archive, export_archive):
        expected_file_path = "memo-3497j.txt"
        expected_archive_path = "archive_path_2jr723"
        expected_archive_dir = "archive_dir_d3aowj2"
        export_service = export.getService()

        export_service._cli.print(expected_archive_dir, [expected_file_path])

        export_archive.assert_called_once_with(expected_archive_path)
        create_archive.assert_called_once_with(
            expected_archive_dir,
            "print_archive.sd-export",
            {"device": "printer"},
            [expected_file_path],
        )

    @patch.object(CLI, "_export_archive", return_value=not_SUCCESS_STATUS)
    @patch.object(Archive, "create_archive")
    def test_print_raises_export_error_when_not_repsonse_not_empty(
        self, create_archive, export_archive
    ):
        valid_archive_dir = "archive_dir_0ngyw"
        valid_file_path = "memo.txt"
        export_service = export.getService()

        with pytest.raises(export.ExportError):
            export_service._cli.print(valid_archive_dir, [valid_file_path])
