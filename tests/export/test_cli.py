import unittest
from unittest.mock import patch

import pytest

from securedrop_client import export
from securedrop_client.export.archive import Archive
from securedrop_client.export.cli import CLI


class TestExportServiceCLIInterface(unittest.TestCase):
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
    def test_printer_status_check_raises_export_error_when_not_USB_CONNECTED(
        self, create_archive, export_archive
    ):
        valid_archive_path = "archive_path_034d3"
        export_service = export.getService()

        with pytest.raises(export.ExportError):
            export_service._cli.check_printer_status(valid_archive_path)
