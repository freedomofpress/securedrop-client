import subprocess
import unittest
from unittest.mock import patch

import pytest

from securedrop_client import export
from securedrop_client.export.archive import Archive
from securedrop_client.export.cli import CLI, Error, Status


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


class TestExportServiceCLIInterfaceWithQubesOS(unittest.TestCase):
    @patch.object(subprocess, "check_output", return_value=b"")
    def test_path_of_exported_archive_is_shell_sanitized(self, subprocess_check_output):
        unsafe_archive_path = "archive_$(path)_../.._4587fn"
        sanitized_archive_path = "'archive_$(path)_../.._4587fn'"
        export_service = export.getService()
        export_service._cli._export_archive(unsafe_archive_path)

        assert subprocess_check_output.called_once()
        subprocess_check_output_arguments = subprocess_check_output.call_args.args[0]
        assert unsafe_archive_path not in subprocess_check_output_arguments
        assert sanitized_archive_path in subprocess_check_output_arguments

    @patch.object(subprocess, "check_output", return_value=b"")
    def test_issues_expected_qrexec_command(self, subprocess_check_output):
        unsafe_archive_path = "archive_$(path)_../.._3wqrc"
        sanitized_archive_path = "'archive_$(path)_../.._3wqrc'"
        export_service = export.getService()

        expected_qrexec_command = [
            "qrexec-client-vm",
            "--",
            "sd-devices",
            "qubes.OpenInVM",
            "/usr/lib/qubes/qopen-in-vm",
            "--view-only",
            "--",
            sanitized_archive_path,
        ]
        expected_execution_options = {"stderr": subprocess.STDOUT}

        export_service._cli._export_archive(unsafe_archive_path)

        assert subprocess_check_output.called_once_with(expected_qrexec_command)

        subprocess_check_output_positional_arguments = subprocess_check_output.call_args.args[0]
        assert subprocess_check_output_positional_arguments == expected_qrexec_command

        subprocess_check_output_keyword_arguments = subprocess_check_output.call_args.kwargs
        assert subprocess_check_output_keyword_arguments == expected_execution_options

    @patch.object(subprocess, "check_output", return_value=b"")
    def test_returns_no_status_when_response_is_empty(self, subprocess_check_output):
        valid_archive_path = "archive_path_sdr3k"
        export_service = export.getService()

        status = export_service._cli._export_archive(valid_archive_path)
        assert status is None

    @patch.object(subprocess, "check_output", return_value=b"whatever")
    def test_returns_status_when_response_is_a_valid_status(self, subprocess_check_output):
        valid_archive_path = "archive_path_32arci"
        export_service = export.getService()

        with pytest.raises(Error) as error:
            export_service._cli._export_archive(valid_archive_path)
        assert error.value.status == Status.UNEXPECTED_RETURN_STATUS

    @patch.object(subprocess, "check_output", return_value=b"USB_CONNECTED")
    def test_raises_UNEXPECTED_RETURN_STATUS_when_response_is_not_a_valid_status(
        self, subprocess_check_output
    ):
        valid_archive_path = "archive_path_pdsa49"
        export_service = export.getService()

        status = export_service._cli._export_archive(valid_archive_path)
        assert status == Status.USB_CONNECTED

    @patch.object(
        subprocess,
        "check_output",
        side_effect=subprocess.CalledProcessError(returncode=1, cmd="..."),
    )
    def test_raises_CALLED_PROCESS_ERROR_when_command_fails(self, subprocess_check_output):
        valid_archive_path = "archive_path_scm3I3"
        export_service = export.getService()

        with pytest.raises(Error) as error:
            export_service._cli._export_archive(valid_archive_path)
        assert error.value.status == Status.CALLED_PROCESS_ERROR
