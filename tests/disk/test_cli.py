import pytest
from unittest import mock

import os
import pytest
import sys

import subprocess

from securedrop_export.enums import ExportEnum
from securedrop_export.disk.cli import CLI
from securedrop_export.disk.volume import EncryptionScheme, Volume
from securedrop_export.exceptions import ExportException
from securedrop_export.disk.status import Status

from securedrop_export.archive import Archive

TEST_CONFIG = os.path.join(os.path.dirname(__file__), "sd-export-config.json")

_DEFAULT_USB_DEVICE = "/dev/sda"
_DEFAULT_USB_DEVICE_ONE_PART = "/dev/sda1"

_PRETEND_LUKS_ID = "luks-id-123456"

# Sample stdout from shell commands
_SAMPLE_OUTPUT_NO_PART = b"disk\ncrypt"  # noqa
_SAMPLE_OUTPUT_ONE_PART = b"disk\npart\ncrypt"  # noqa
_SAMPLE_OUTPUT_MULTI_PART = b"disk\npart\npart\npart\ncrypt"  # noqa
_SAMPLE_OUTPUT_USB = b"/dev/sda"  # noqa

_SAMPLE_LUKS_HEADER = b"\n\nUUID:\t123456-DEADBEEF"  # noqa


class TestCli:
    """
    Test the CLI wrapper that handless identification and locking/unlocking of
    USB volumes.
    """

    def _setup_usb_devices(self, mocker, disks, is_removable):
        """
        Helper function to set up mocked shell calls representing
        the search for attached USB devices.
        The original calls are `lsblk | grep disk` and
        `cat /sys/class/block/{disk}/removable`

        Parameters:
            disks (byte array): Array of disk names separated by newline.
            is_removable (byte array): Array of removable status results (1 for removable) separated by newline
        """

        # Patch commandline calls to `lsblk | grep disk`
        command_output = mock.MagicMock()
        command_output.stdout = mock.MagicMock()
        command_output.stdout.readlines = mock.MagicMock(return_value=disks)
        mocker.patch("subprocess.Popen", return_value=command_output)

        # Pactch commandline call to 'cat /sys/class/block/{device}/removable'

        # Using side_effect with an iterable allows for different return value each time,
        # which matches what would happen if iterating through list of devices
        mocker.patch("subprocess.check_output", side_effect=is_removable)

    def test_get_connected_devices(self, mocker):
        disks = [b"sda disk\n", b"sdb disk\n"]
        removable = [b"1\n", b"1\n"]

        self._setup_usb_devices(mocker, disks, removable)
        cli = CLI()
        result = cli.get_connected_devices()

        assert result[0] == "/dev/sda" and result[1] == "/dev/sdb"

    @mock.patch("subprocess.Popen", side_effect=subprocess.CalledProcessError(1, "Popen"))
    def test_get_connected_devices_error(self, mocked_subprocess):
        cli = CLI()

        with pytest.raises(ExportException):
            cli.get_connected_devices()

    @mock.patch("subprocess.check_output", return_value=_SAMPLE_OUTPUT_NO_PART)
    def test_get_partitioned_device_no_partition(self, mocked_call):
        cli = CLI()

        result = cli.get_partitioned_device(_DEFAULT_USB_DEVICE)
        assert result == _DEFAULT_USB_DEVICE

    @mock.patch("subprocess.check_output", return_value=_SAMPLE_OUTPUT_ONE_PART)
    def test_get_partitioned_device_one_partition(self, mocked_call):
        cli = CLI()

        result = cli.get_partitioned_device(_DEFAULT_USB_DEVICE)
        assert result == _DEFAULT_USB_DEVICE+"1"

    @mock.patch("subprocess.check_output", return_value=_SAMPLE_OUTPUT_MULTI_PART)
    def test_get_partitioned_device_multi_partition(self, mocked_call):
        cli = CLI()

        with pytest.raises(ExportException):
            result = cli.get_partitioned_device(_SAMPLE_OUTPUT_MULTI_PART)

    @mock.patch(
        "subprocess.check_output", side_effect=subprocess.CalledProcessError(1, "check_output")
    )
    def test_get_partitioned_device_multi_partition_error(self, mocked_call):
        cli = CLI()

        # Make sure we wrap CalledProcessError and throw our own exception
        with pytest.raises(ExportException):
            cli.get_partitioned_device(_DEFAULT_USB_DEVICE)

    @mock.patch("subprocess.check_call", return_value=0)
    def test_is_luks_volume_true(self, mocked_call):
        cli = CLI()

        # `sudo cryptsetup isLuks` returns 0 if true
        assert cli.is_luks_volume(_SAMPLE_OUTPUT_ONE_PART)

    @mock.patch("subprocess.check_call", side_effect=subprocess.CalledProcessError(1, "check_call"))
    def test_is_luks_volume_false(self, mocked_subprocess):
        cli = CLI()

        # `sudo cryptsetup isLuks` returns 1 if false; CalledProcessError is thrown
        assert not cli.is_luks_volume(_SAMPLE_OUTPUT_ONE_PART)

    @mock.patch("subprocess.check_output", return_value=_SAMPLE_LUKS_HEADER)
    def test__get_luks_name_from_headers(self, mocked_subprocess):
        cli = CLI()

        result = cli._get_luks_name_from_headers(_DEFAULT_USB_DEVICE)

        assert result is not None and result.split("-")[1] in _SAMPLE_LUKS_HEADER.decode("utf8")

    @mock.patch("subprocess.check_output", return_value=b"corrupted-or-invalid-header\n")
    def test__get_luks_name_from_headers_error(self, mocked_subprocess):
        cli = CLI()

        with pytest.raises(ExportException):
            result = cli._get_luks_name_from_headers(_DEFAULT_USB_DEVICE)

    @mock.patch(
        "subprocess.check_output", side_effect=subprocess.CalledProcessError(1, "check_output")
    )
    def test__get_luks_name_from_headers_error(self, mocked_subprocess):
        cli = CLI()

        with pytest.raises(ExportException):
            result = cli._get_luks_name_from_headers(_DEFAULT_USB_DEVICE)

    @mock.patch("os.path.exists", return_value=True)
    @mock.patch("subprocess.check_output", return_value=_SAMPLE_LUKS_HEADER)
    def test_get_luks_volume_already_unlocked(self, mocked_subprocess, mocked_os_call):
        cli = CLI()
        result = cli.get_luks_volume(_DEFAULT_USB_DEVICE_ONE_PART)

        assert result.encryption is EncryptionScheme.LUKS
        assert result.unlocked

    @mock.patch("os.path.exists", return_value=True)
    def test__unlock_luks_volume_success(self, mocker):
        cli = CLI()

        mock_popen = mocker.MagicMock()
        mock_popen_communicate = mocker.MagicMock()
        mock_popen.returncode = 0

        mocker.patch("subprocess.Popen", return_value=mock_popen)
        mocker.patch("subprocess.Popen.communicate", return_value=mock_popen_communicate)

        mapped_name = "luks-id-123456"
        vol = Volume(device_name=_DEFAULT_USB_DEVICE, mapped_name=mapped_name, encryption=EncryptionScheme.LUKS)
        key = "A key!&8*%_ A KEY"
        result = cli.unlock_luks_volume(vol, key)
        assert vol.unlocked

    def test_unlock_luks_volume_not_luks(self, mocker):
        cli = CLI()

        mock_popen = mocker.MagicMock()
        mock_popen.communicate = mocker.MagicMock()
        mock_popen.communicate.returncode = 1  # An error unlocking

        mocker.patch("subprocess.Popen", mock_popen)

        vol = Volume(device_name=_DEFAULT_USB_DEVICE, mapped_name=_PRETEND_LUKS_ID, encryption=EncryptionScheme.UNKNOWN)
        key = "a key!"
        mapped_name = "luks-id-123456"

        with pytest.raises(ExportException):
            cli.unlock_luks_volume(vol, key)

    def test_unlock_luks_volume_passphrase_failure(self, mocker):
        cli = CLI()

        mock_popen = mocker.MagicMock()
        mock_popen.communicate = mocker.MagicMock()
        mock_popen.communicate.returncode = 1  # An error unlocking

        mocker.patch("subprocess.Popen", mock_popen)

        vol = Volume(device_name=_DEFAULT_USB_DEVICE, mapped_name=_PRETEND_LUKS_ID, encryption=EncryptionScheme.LUKS)
        key = "a key!"
        mapped_name = "luks-id-123456"

        with pytest.raises(ExportException):
            cli.unlock_luks_volume(vol, key)

    @mock.patch("subprocess.Popen", side_effect=subprocess.CalledProcessError("1", "Popen"))
    def test_unlock_luks_volume_luksOpen_exception(self, mocked_subprocess):
        cli = CLI()
        pd = Volume(device_name=_DEFAULT_USB_DEVICE, mapped_name=_PRETEND_LUKS_ID, encryption=EncryptionScheme.LUKS)
        key = "a key!"
        mapped_name = "luks-id-123456"

        with pytest.raises(ExportException):
            cli.unlock_luks_volume(pd, key)

    @mock.patch("os.path.exists", return_value=True)
    @mock.patch("subprocess.check_output", return_value=b"\n")
    @mock.patch("subprocess.check_call", return_value=0)
    def test_mount_volume(self, mocked_output, mocked_call, mocked_path):
        cli = CLI()
        vol = Volume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            encryption=EncryptionScheme.LUKS,
        )
        result = cli.mount_volume(vol)

    @mock.patch("os.path.exists", return_value=True)
    @mock.patch("subprocess.check_output", return_value=b"/dev/pretend/luks-id-123456\n")
    @mock.patch("subprocess.check_call", return_value=0)
    def test_mount_volume_already_mounted(self, mocked_output, mocked_call, mocked_path):
        cli = CLI()
        md = Volume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            encryption=EncryptionScheme.LUKS,
        )
        result = cli.mount_volume(md)

    @mock.patch("os.path.exists", return_value=True)
    @mock.patch("subprocess.check_output", return_value=b"\n")
    @mock.patch("subprocess.check_call", return_value=0)
    def test_mount_volume_mkdir(self, mocked_output, mocked_subprocess, mocked_path):
        cli = CLI()
        md = Volume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            encryption=EncryptionScheme.LUKS,
        )
        result = cli.mount_volume(md)

        assert result.mapped_name == _PRETEND_LUKS_ID

    @mock.patch("subprocess.check_output", return_value=b"\n")
    @mock.patch("subprocess.check_call", side_effect=subprocess.CalledProcessError(1, "check_call"))
    def test_mount_volume_error(self, mocked_subprocess, mocked_output):
        cli = CLI()

        md = Volume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            encryption=EncryptionScheme.LUKS,
        )

        with pytest.raises(ExportException):
            cli.mount_volume(md)

    @mock.patch("os.path.exists", return_value=True)
    @mock.patch("subprocess.check_call", return_value=0)
    def test__unmount_volume(self, mocked_subprocess, mocked_mountpath):
        cli = CLI()

        mounted = Volume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            mountpoint=cli._DEFAULT_MOUNTPOINT,
            encryption=EncryptionScheme.LUKS,
        )

        result = cli._unmount_volume(mounted)


    @mock.patch("os.path.exists", return_value=True)
    @mock.patch("subprocess.check_call", side_effect=subprocess.CalledProcessError(1, "check_call"))
    def test__unmount_volume_error(self, mocked_subprocess, mocked_mountpath):
        cli = CLI()

        mounted = Volume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            mountpoint=cli._DEFAULT_MOUNTPOINT,
            encryption=EncryptionScheme.LUKS,
        )

        with pytest.raises(ExportException):
            result = cli._unmount_volume(mounted)

    @mock.patch("os.path.exists", return_value=True)
    @mock.patch("subprocess.check_call", return_value=0)
    def test__close_luks_volume(self, mocked_subprocess, mocked_os_call):
        cli = CLI()

        mapped = Volume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            encryption=EncryptionScheme.LUKS,
        )

        # If call completes without error, drive was successfully closed with luksClose
        cli._close_luks_volume(mapped)

    @mock.patch("os.path.exists", return_value=True)
    @mock.patch("subprocess.check_call", side_effect=subprocess.CalledProcessError(1, "check_call"))
    def test__close_luks_volume_error(self, mocked_subprocess, mocked_os_call):
        cli = CLI()

        mapped = Volume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            encryption=EncryptionScheme.LUKS,
        )

        with pytest.raises(ExportException):
            cli._close_luks_volume(mapped)

    @mock.patch("subprocess.check_call", side_effect=subprocess.CalledProcessError(1, "check_call"))
    def test__remove_temp_directory_error(self, mocked_subprocess):
        cli = CLI()

        with pytest.raises(ExportException):
            cli._remove_temp_directory("tmp")

    @mock.patch("subprocess.check_call", return_value=0)
    def test_write_to_disk(self, mock_check_call):
        cli = CLI()

        vol = Volume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            mountpoint=cli._DEFAULT_MOUNTPOINT,
            encryption=EncryptionScheme.LUKS,
        )

        submission = Archive("testfile", TEST_CONFIG)

        cli.write_data_to_device(submission.tmpdir, submission.target_dirname, vol)

    @mock.patch("subprocess.check_call", side_effect=subprocess.CalledProcessError(1, "check_call"))
    def test_write_to_disk_error_still_does_cleanup(self, mock_call, mocker):
        cli = CLI()
        cli.cleanup_drive_and_tmpdir = mocker.MagicMock()

        vol = Volume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            mountpoint=cli._DEFAULT_MOUNTPOINT,
            encryption=EncryptionScheme.LUKS,
        )
        submission = Archive("testfile", TEST_CONFIG)

        with pytest.raises(ExportException):
            cli.write_data_to_device(submission.tmpdir, submission.target_dirname, vol)
            cleanup_mock.assert_called_once()

