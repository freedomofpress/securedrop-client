import unittest
from unittest.mock import patch

from PyQt5.QtTest import QSignalSpy

from securedrop_client import export


class TestExportServicePrinterInterface(unittest.TestCase):
    @patch(
        "securedrop_client.export.service.TemporaryDirectory.__enter__",
        return_value="tmpdir-sq324f",
    )
    @patch.object(export.Service, "_check_printer_status")
    def test_uses_temporary_directory_for_printer_status_check(
        self, _check_printer_status, _tmpdir
    ):
        export_service = export.Service()

        export_service.check_printer_status()

        _check_printer_status.assert_called_once_with("tmpdir-sq324f")

    @patch("securedrop_client.export.service.TemporaryDirectory")
    @patch.object(export.Service, "_check_printer_status")
    def test_emits_printer_found_ready_when_printer_status_check_succeeds(
        self, _check_printer_status, _temporary_directory
    ):
        export_service = export.Service()
        printer_found_ready_emissions = QSignalSpy(export_service.printer_found_ready)
        assert printer_found_ready_emissions.isValid()

        export_service.check_printer_status()

        assert len(printer_found_ready_emissions) == 1
        assert printer_found_ready_emissions[0] == []

    @patch("securedrop_client.export.service.TemporaryDirectory")
    @patch.object(export.Service, "_check_printer_status")
    def test_emits_printer_not_found_ready_when_printer_status_check_fails(
        self, _check_printer_status, _temporary_directory
    ):
        expected_error = export.ExportError("bang!")
        _check_printer_status.side_effect = expected_error
        export_service = export.Service()
        printer_not_found_ready_emissions = QSignalSpy(export_service.printer_not_found_ready)
        assert printer_not_found_ready_emissions.isValid()

        export_service.check_printer_status()

        assert len(printer_not_found_ready_emissions) == 1
        assert printer_not_found_ready_emissions[0] == [expected_error]

    # FIXME Add disk API tests