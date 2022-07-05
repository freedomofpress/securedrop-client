from unittest import mock

import os
import pytest
import sys

from subprocess import CalledProcessError

from securedrop_export import export
from securedrop_export.disk.actions import DiskExportAction, DiskTestAction

TEST_CONFIG = os.path.join(os.path.dirname(__file__), "sd-export-config.json")
SAMPLE_OUTPUT_NO_PART = b"disk\ncrypt"  # noqa
SAMPLE_OUTPUT_ONE_PART = b"disk\npart\ncrypt"  # noqa
SAMPLE_OUTPUT_MULTI_PART = b"disk\npart\npart\npart\ncrypt"  # noqa
SAMPLE_OUTPUT_USB = b"/dev/sda"  # noqa


def test_usb_precheck_disconnected(capsys, mocker):
    """Tests the scenario where there are disks connected, but none of them are USB"""
    submission = export.SDExport("testfile", TEST_CONFIG)
    action = DiskTestAction(submission)
    expected_message = "USB_NOT_CONNECTED"
    assert export.ExportStatus.USB_NOT_CONNECTED.value == expected_message

    # Popen call returns lsblk output
    command_output = mock.MagicMock()
    command_output.stdout = mock.MagicMock()
    command_output.stdout.readlines = mock.MagicMock(
        return_value=[b"sda disk\n", b"sdb disk\n"]
    )
    mocker.patch("subprocess.Popen", return_value=command_output)

    # check_output returns removable status
    mocker.patch("subprocess.check_output", return_value=[b"0\n", b"0\n"])

    mocked_exit = mocker.patch.object(submission, "exit_gracefully", return_value=0)

    mocker.patch(
        "subprocess.check_output", side_effect=CalledProcessError(1, "check_output")
    )

    action.check_usb_connected(exit=True)

    mocked_exit.assert_called_once_with(expected_message)
    assert action.device is None


def test_usb_precheck_connected(capsys, mocker):
    """Tests the scenario where there is one USB connected"""
    submission = export.SDExport("testfile", TEST_CONFIG)
    action = DiskTestAction(submission)

    # Popen call returns lsblk output
    command_output = mock.MagicMock()
    command_output.stdout = mock.MagicMock()
    command_output.stdout.readlines = mock.MagicMock(return_value=[b"sdb disk\n"])
    mocker.patch("subprocess.Popen", return_value=command_output)

    # check_output returns removable status
    mocker.patch("subprocess.check_output", return_value=b"1\n")

    expected_message = "USB_CONNECTED"
    assert export.ExportStatus.USB_CONNECTED.value == expected_message
    mocked_exit = mocker.patch.object(submission, "exit_gracefully", return_value=0)

    action.check_usb_connected(exit=True)

    mocked_exit.assert_called_once_with(expected_message)
    assert action.device == "/dev/sdb"


def test_usb_precheck_multiple_devices_connected(capsys, mocker):
    """Tests the scenario where there are multiple USB drives connected"""
    submission = export.SDExport("testfile", TEST_CONFIG)
    action = DiskTestAction(submission)

    # Popen call returns lsblk output
    command_output = mock.MagicMock()
    command_output.stdout = mock.MagicMock()
    command_output.stdout.readlines = mock.MagicMock(
        return_value=[b"sdb disk\n", b"sdc disk\n"]
    )
    mocker.patch("subprocess.Popen", return_value=command_output)

    # check_output returns removable status
    mocker.patch("subprocess.check_output", return_value=b"1\n")

    expected_message = "ERROR_GENERIC"
    assert export.ExportStatus.ERROR_GENERIC.value == expected_message
    mocked_exit = mocker.patch.object(submission, "exit_gracefully", return_value=0)

    action.check_usb_connected(exit=True)

    mocked_exit.assert_called_once_with(expected_message)
    assert action.device is None


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_NO_PART)
def test_extract_device_name_no_part(mocked_call, capsys):
    submission = export.SDExport("testfile", TEST_CONFIG)
    action = DiskExportAction(submission)

    action.device = "/dev/sda"

    action.set_extracted_device_name()

    assert action.device == "/dev/sda"


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_ONE_PART)
def test_extract_device_name_single_part(mocked_call, capsys):
    submission = export.SDExport("testfile", TEST_CONFIG)
    action = DiskExportAction(submission)

    action.device = "/dev/sda"

    action.set_extracted_device_name()

    assert action.device == "/dev/sda1"


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_MULTI_PART)
def test_extract_device_name_multiple_part(mocked_call, capsys, mocker):
    submission = export.SDExport("testfile", TEST_CONFIG)
    action = DiskExportAction(submission)
    action.device = "/dev/sda"
    mocked_exit = mocker.patch.object(submission, "exit_gracefully", return_value=0)
    expected_message = export.ExportStatus.USB_ENCRYPTION_NOT_SUPPORTED.value

    action.set_extracted_device_name()

    mocked_exit.assert_called_once_with(expected_message)


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_NO_PART)
def test_luks_precheck_encrypted_fde(mocked_call, capsys, mocker):
    submission = export.SDExport("testfile", TEST_CONFIG)
    action = DiskExportAction(submission)

    command_output = mock.MagicMock()
    command_output.stderr = b""
    mocker.patch("subprocess.run", return_value=command_output)

    expected_message = export.ExportStatus.USB_ENCRYPTED.value
    mocked_exit = mocker.patch.object(submission, "exit_gracefully", return_value=0)

    action.check_luks_volume()

    mocked_exit.assert_called_once_with(expected_message)


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_ONE_PART)
def test_luks_precheck_encrypted_single_part(mocked_call, capsys, mocker):
    submission = export.SDExport("testfile", TEST_CONFIG)
    action = DiskExportAction(submission)
    action.device = "/dev/sda"
    expected_message = export.ExportStatus.USB_ENCRYPTED.value
    mocked_exit = mocker.patch.object(submission, "exit_gracefully", return_value=0)

    command_output = mock.MagicMock()
    command_output.stderr = b""
    mocker.patch("subprocess.run", return_value=command_output)

    action.check_luks_volume()

    mocked_exit.assert_called_once_with(expected_message)


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_MULTI_PART)
def test_luks_precheck_encrypted_multi_part(mocked_call, capsys, mocker):
    submission = export.SDExport("testfile", TEST_CONFIG)
    action = DiskExportAction(submission)
    action.device = "/dev/sda"
    expected_message = export.ExportStatus.USB_ENCRYPTION_NOT_SUPPORTED.value

    # Here we need to mock the exit_gracefully method with a side effect otherwise
    # program execution will continue after exit_gracefully and exit_gracefully
    # may be called a second time.
    mocked_exit = mocker.patch.object(
        submission, "exit_gracefully", side_effect=lambda x: sys.exit(0)
    )

    # Output of `lsblk -o TYPE --noheadings DEVICE_NAME` when a drive has multiple
    # partitions
    multi_partition_lsblk_output = b"disk\npart\npart\n"
    mocker.patch("subprocess.check_output", return_value=multi_partition_lsblk_output)

    with pytest.raises(SystemExit):
        action.check_luks_volume()

    mocked_exit.assert_called_once_with(expected_message)


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_ONE_PART)
def test_luks_precheck_encrypted_luks_error(mocked_call, capsys, mocker):
    submission = export.SDExport("testfile", TEST_CONFIG)
    action = DiskExportAction(submission)
    action.device = "/dev/sda"
    expected_message = "USB_ENCRYPTION_NOT_SUPPORTED"
    assert expected_message == export.ExportStatus.USB_ENCRYPTION_NOT_SUPPORTED.value

    mocked_exit = mocker.patch.object(
        submission, "exit_gracefully", side_effect=lambda msg, e: sys.exit(0)
    )

    single_partition_lsblk_output = b"disk\npart\n"
    mocker.patch("subprocess.check_output", return_value=single_partition_lsblk_output)
    mocker.patch("subprocess.run", side_effect=CalledProcessError(1, "run"))

    with pytest.raises(SystemExit):
        action.check_luks_volume()

    assert mocked_exit.mock_calls[0][2]["msg"] == expected_message
    assert mocked_exit.mock_calls[0][2]["e"] is None
