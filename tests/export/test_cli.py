import unittest
from unittest.mock import MagicMock

import pytest

from securedrop_client import export


class TestExportServiceCLIInterface(unittest.TestCase):
    def test_printer_status_check_returns_without_errors_when_empty_response(self):
        SUCCESS_STATUS = ""  # sd-devices API
        export_service = export.Service()
        valid_archive_path = "archive_path_13kn3"
        export_service._create_archive = MagicMock()
        export_service._export_archive = MagicMock(return_value=SUCCESS_STATUS)

        export_service._check_printer_status(valid_archive_path)

        assert True  # no exception was raised

    def test_printer_status_check_exports_a_specifically_created_archive(self):
        expected_archive_path = "archive_path_9f483f"
        expected_archive_dir = "archive_dir_2i19c"
        export_service = export.Service()
        export_service._create_archive = MagicMock(return_value=expected_archive_path)
        export_service._export_archive = MagicMock(return_value="")  # "magic" value

        export_service._check_printer_status(expected_archive_dir)

        export_service._export_archive.assert_called_once_with(expected_archive_path)
        export_service._create_archive.assert_called_once_with(
            expected_archive_dir, "printer-preflight.sd-export", {"device": "printer-preflight"}
        )

    def test_printer_status_check_raises_export_error_when_not_USB_CONNECTED(self):
        not_USB_CONNECTED = "whatever"
        valid_archive_path = "archive_path_034d3"
        export_service = export.Service()
        export_service._create_archive = MagicMock()
        export_service._export_archive = MagicMock(return_value=not_USB_CONNECTED)

        with pytest.raises(export.ExportError):
            export_service._check_printer_status(valid_archive_path)
