import pytest
from unittest import mock

import os
import pytest
import sys
import tempfile

import subprocess
from subprocess import CalledProcessError

from securedrop_export.disk.exceptions import ExportException
from securedrop_export.disk.status import Status

from securedrop_export import export
from securedrop_export.disk.actions import DiskExportAction, DiskTestAction, USBTestAction

TEST_CONFIG = os.path.join(os.path.dirname(__file__), "sd-export-config.json")
SAMPLE_OUTPUT_LSBLK_NO_PART = b"disk\ncrypt"  # noqa
SAMPLE_OUTPUT_LSBLK_ONE_PART = b"disk\npart\ncrypt"  # noqa
SAMPLE_OUTPUT_LSBLK_MULTI_PART = b"disk\npart\npart\npart\ncrypt"  # noqa
SAMPLE_OUTPUT_USB = b"/dev/sda"  # noqa


class TestExportAction:
    def _setup_submission(self) -> export.SDExport:
        """
        Helper method to set up stub export object
        """
        submission = export.SDExport("testfile", TEST_CONFIG)
        temp_folder = tempfile.mkdtemp()
        metadata = os.path.join(temp_folder, export.Metadata.METADATA_FILE)
        with open(metadata, "w") as f:
            f.write('{"device": "disk", "encryption_method": "luks", "encryption_key": "hunter1"}')

        submission.archive_metadata = export.Metadata(temp_folder)

        return submission

    @mock.patch("sys.exit")
    @mock.patch("securedrop_export.disk.actions.CLI")
    def test_run_usbtestaction(self, mock_cli, mock_sys,):

        mock_cli.write_status = mock.MagicMock()
        usb = USBTestAction(self._setup_submission())

        usb.run()
        mock_cli.write_status.assert_called_once_with(Status.LEGACY_USB_CONNECTED)


    @mock.patch("securedrop_export.disk.actions.CLI")
    def test_run_usbtestaction_error(self, mock_cli, capsys):
        mock_cli.get_connected_devices.side_effect = ExportException(Status.LEGACY_ERROR_USB_CHECK)
        usb = USBTestAction(self._setup_submission())

        mock_cli.write_status = mock.MagicMock()
        
        usb.run()
        mock_cli.write_status.assert_called_once_with(Status.LEGACY_ERROR_USB_CHECK)

    @mock.patch("sys.exit")
    @mock.patch("securedrop_export.disk.actions.CLI")
    def test_run_disktestaction(self, mock_sys, mock_cli):

        mock_cli.is_luks_volume.return_value=True
        mock_cli.write_status = mock.MagicMock()

        test_export = DiskTestAction(self._setup_submission())
        test_export.run()

        mock_cli.write_status.assert_called_once_with(Status.SUCCESS_EXPORT)

    @mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_LSBLK_NO_PART)
    @mock.patch("subprocess.check_call", return_value=0)
    def test_luks_precheck_encrypted_fde(mocked_call, capsys, mocker):
        submission = export.SDExport("testfile", TEST_CONFIG)
        action = DiskExportAction(submission)

        command_output = mock.MagicMock()
        command_output.stderr = b""
        mocker.patch("subprocess.run", return_value=command_output)

        expected_message = Status.LEGACY_USB_ENCRYPTED.value
        mocked_exit = mocker.patch.object(submission, "exit_gracefully", return_value=0)

    @mock.patch("sys.exit")
    @mock.patch("securedrop_export.disk.actions.CLI")
    def test_run_disktestaction_error(self, mock_cli, mocker):
        mock_cli.patch("get_partitioned_device", side_effect=ExportException(Status.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED))

        status_mock = mock_cli.patch("write_status")
        test_export = DiskTestAction(self._setup_submission())
        test_export.run()
        status_mock.assert_called_once_with(Status.LEGACY_ERROR_USB_WRITE)

    @mock.patch("sys.exit")
    @mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_LSBLK_ONE_PART)
    @mock.patch("subprocess.check_call", return_value=0)
    def test_luks_precheck_encrypted_single_part(mocked_call, mock_output, capsys, mocker):
        submission = export.SDExport("testfile", TEST_CONFIG)
        action = DiskTestAction(submission)
        action.device = "/dev/sda"
        expected_message = Status.LEGACY_USB_ENCRYPTED.value
        mocked_exit = mocker.patch.object(submission, "exit_gracefully", return_value=0)

        command_output = mock.MagicMock()
        command_output.stderr = b""
        mocker.patch("subprocess.run", return_value=command_output)

        action.run()

    @mock.patch("sys.exit")
    @mock.patch("securedrop_export.disk.actions.CLI")
    def test_run_diskexportaction(self, mock_cli, mock_sys):

        mock_cli.patch("is_luks_volume", return_value=True)
        status_mock = mock_cli.patch("write_status")

        test_export = DiskExportAction(self._setup_submission())
        test_export.run()

        status_mock.assert_called_once_with(Status.SUCCESS_EXPORT)

    @mock.patch("sys.exit")
    @mock.patch("securedrop_export.disk.actions.CLI")
    def test_run_diskexportaction_disk_not_supported(self, mock_cli, mock_sys):

        mock_cli.patch("get_partitioned_device")
        mock_cli.patch("is_luks_volume", return_value=False)
        status_mock = mock_cli.patch("write_status")

        test_export = DiskExportAction(self._setup_submission())
        test_export.run()

        status_mock.assert_called_once_with(Status.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED)

    @mock.patch("sys.exit")
    @mock.patch("securedrop_export.disk.actions.CLI")
    def test_run_diskexportaction_not_supported(self, mock_sys, mock_cli):

        status_mock = mock_cli.patch("write_status")
        mock_cli.patch("get_partitioned_device")
        mock_cli.is_luks_volume.return_value=True
        mock_cli.write_data_to_device.side_effect = Status.LEGACY_ERROR_USB_WRITE

        test_export = DiskExportAction(self._setup_submission())
        test_export.run()

        status_mock.assert_called_once_with(Status.LEGACY_ERROR_USB_WRITE)
