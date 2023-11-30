import pytest
from unittest import mock

import subprocess

from securedrop_export.disk.cli import CLI
from securedrop_export.disk.volume import EncryptionScheme, Volume, MountedVolume
from securedrop_export.exceptions import ExportException
from securedrop_export.disk.status import Status

from securedrop_export.archive import Archive

_DEFAULT_USB_DEVICE = "/dev/sda"
_DEFAULT_USB_DEVICE_ONE_PART = "/dev/sda1"

_PRETEND_LUKS_ID = "luks-id-123456"

# Sample stdout from shell commands
_SAMPLE_OUTPUT_NO_PART = b"disk\ncrypt"  # noqa
_SAMPLE_OUTPUT_ONE_PART = b"disk\npart\ncrypt"  # noqa
_SAMPLE_OUTPUT_MULTI_PART = b"disk\npart\npart\npart\ncrypt"  # noqa
_SAMPLE_OUTPUT_USB = b"/dev/sda"  # noqa

_SAMPLE_LUKS_HEADER = b"\n\nUUID:\t123456-DEADBEEF"  # noqa
_SAMPLE_CRYPTSETUP_STATUS_OUTPUT = b"/dev/mapper/vc is active and is in use.\n  type:    \
TCRYPT\n  cipher:  aes-xts-plain64\n  keysize: 512 bits\n  key location: dm-crypt\n  device:  \
/dev/sdc\n  sector size:  512\n  mode:    read/write\n"
_SAMPLE_MOUNTED_VC_OUTPUT = b"/media/custom_mount"

_EXAMPLE_MOUNTPOINT = "/media/usb"


class TestCli:
    """
    Test the CLI wrapper that handless identification and locking/unlocking of
    USB volumes.
    """

    @classmethod
    def setup_class(cls):
        cls.cli = CLI()

    @classmethod
    def teardown_class(cls):
        cls.cli = None

    def _setup_usb_devices(self, mocker, disks, is_removable):
        """
        Helper function to set up mocked shell calls representing
        the search for attached USB devices.
        The original calls are `lsblk | grep disk` and
        `cat /sys/class/block/{disk}/removable`

        Parameters:
            disks (byte array): Array of disk names separated by newline.
            is_removable (byte array): Array of removable status results (1 for removable),
            separated by newline
        """

        # Patch commandline calls to `lsblk | grep disk`
        command_output = mock.MagicMock()
        command_output.stdout = mock.MagicMock()
        command_output.stdout.readlines = mock.MagicMock(return_value=disks)
        mocker.patch("subprocess.Popen", return_value=command_output)

        # Patch commandline call to 'cat /sys/class/block/{device}/removable'

        # Using side_effect with an iterable allows for different return value each time,
        # which matches what would happen if iterating through list of devices
        mocker.patch("subprocess.check_output", side_effect=is_removable)

    def test__get_connected_devices(self, mocker):
        disks = [b"sda disk\n", b"sdb disk\n"]
        removable = [b"1\n", b"1\n"]

        self._setup_usb_devices(mocker, disks, removable)
        result = self.cli._get_connected_devices()

        assert result[0] == "/dev/sda" and result[1] == "/dev/sdb"

    @mock.patch(
        "subprocess.check_output",
        side_effect=subprocess.CalledProcessError(1, "check_output"),
    )
    def test_get_removable_devices_none_removable(self, mocker):
        disks = [b"sda disk\n", b"sdb disk\n"]
        removable = [b"0\n", b"0\n"]

        self._setup_usb_devices(mocker, disks, removable)

        result = self.cli._get_removable_devices(disks)
        assert len(result) == 0

    @mock.patch(
        "subprocess.Popen", side_effect=subprocess.CalledProcessError(1, "Popen")
    )
    def test__get_connected_devices_error(self, mocked_subprocess):
        with pytest.raises(ExportException):
            self.cli._get_connected_devices()

    @mock.patch("subprocess.check_output", return_value=_SAMPLE_OUTPUT_NO_PART)
    def test__get_partitioned_device_no_partition(self, mocked_call):
        assert (
            self.cli._get_partitioned_device(_DEFAULT_USB_DEVICE) == _DEFAULT_USB_DEVICE
        )

    @mock.patch("subprocess.check_output", return_value=_SAMPLE_OUTPUT_ONE_PART)
    def test__get_partitioned_device_one_partition(self, mocked_call):
        assert (
            self.cli._get_partitioned_device(_DEFAULT_USB_DEVICE)
            == _DEFAULT_USB_DEVICE + "1"
        )

    @mock.patch("subprocess.check_output", return_value=_SAMPLE_OUTPUT_MULTI_PART)
    def test__get_partitioned_device_multi_partition(self, mocked_call):
        with pytest.raises(ExportException) as ex:
            self.cli._get_partitioned_device(_SAMPLE_OUTPUT_MULTI_PART)

        assert ex.value.sdstatus is Status.INVALID_DEVICE_DETECTED

    @mock.patch("subprocess.check_output", return_value=None)
    def test__get_partitioned_device_lsblk_error(self, mocked_subprocess):
        with pytest.raises(ExportException) as ex:
            self.cli._get_partitioned_device(_SAMPLE_OUTPUT_ONE_PART)

        assert ex.value.sdstatus is Status.DEVICE_ERROR

    @mock.patch(
        "subprocess.check_output",
        side_effect=subprocess.CalledProcessError(1, "check_output"),
    )
    def test__get_partitioned_device_multi_partition_error(self, mocked_call):
        # Make sure we wrap CalledProcessError and throw our own exception
        with pytest.raises(ExportException) as ex:
            self.cli._get_partitioned_device(_DEFAULT_USB_DEVICE)

        assert ex.value.sdstatus is Status.DEVICE_ERROR

    @mock.patch("subprocess.check_call", return_value=0)
    def test_is_luks_volume_true(self, mocked_call):
        # `sudo cryptsetup isLuks` returns 0 if true
        assert self.cli.is_luks_volume(_SAMPLE_OUTPUT_ONE_PART)

    @mock.patch(
        "subprocess.check_call",
        side_effect=subprocess.CalledProcessError(1, "check_call"),
    )
    def test_is_luks_volume_false(self, mocked_subprocess):
        # `sudo cryptsetup isLuks` returns 1 if false; CalledProcessError is thrown
        assert not self.cli.is_luks_volume(_SAMPLE_OUTPUT_ONE_PART)

    @mock.patch("subprocess.check_output", return_value=_SAMPLE_LUKS_HEADER)
    def test__get_luks_name_from_headers(self, mocked_subprocess):
        result = self.cli._get_luks_name_from_headers(_DEFAULT_USB_DEVICE)

        assert result is not None and result.split("-")[
            1
        ] in _SAMPLE_LUKS_HEADER.decode("utf8")

    @mock.patch(
        "subprocess.check_output", return_value=b"corrupted-or-invalid-header\n"
    )
    def test__get_luks_name_from_headers_error_invalid(self, mocked_subprocess):
        with pytest.raises(ExportException) as ex:
            self.cli._get_luks_name_from_headers(_DEFAULT_USB_DEVICE)

        assert ex.value.sdstatus is Status.INVALID_DEVICE_DETECTED

    @mock.patch("subprocess.check_output", return_value=b"\n")
    def test__get_luks_name_from_headers_error_no_header(self, mocked_subprocess):
        with pytest.raises(ExportException) as ex:
            self.cli._get_luks_name_from_headers(_DEFAULT_USB_DEVICE)

        assert ex.value.sdstatus is Status.INVALID_DEVICE_DETECTED

    @mock.patch("subprocess.check_output", return_value=None)
    def test__get_luks_name_from_headers_error_nothing_returned(
        self, mocked_subprocess
    ):
        with pytest.raises(ExportException) as ex:
            self.cli._get_luks_name_from_headers(_DEFAULT_USB_DEVICE)

        assert ex.value.sdstatus is Status.INVALID_DEVICE_DETECTED

    @mock.patch(
        "subprocess.check_output",
        side_effect=subprocess.CalledProcessError(1, "check_output"),
    )
    def test__get_luks_name_from_headers_error(self, mocked_subprocess):
        with pytest.raises(ExportException):
            self.cli._get_luks_name_from_headers(_DEFAULT_USB_DEVICE)

    @mock.patch("os.path.exists", return_value=True)
    @mock.patch("subprocess.check_output", return_value=_SAMPLE_LUKS_HEADER)
    def test__get_luks_volume_already_unlocked(self, mocked_subprocess, mocked_os_call):
        result = self.cli._get_luks_volume(_DEFAULT_USB_DEVICE_ONE_PART)

        assert result.encryption is EncryptionScheme.LUKS
        assert result.unlocked

    @mock.patch("os.path.exists", return_value=False)
    @mock.patch("subprocess.check_output", return_value=_SAMPLE_LUKS_HEADER)
    def test__get_luks_volume_still_locked(self, mocked_subprocess, mocked_os_call):
        result = self.cli._get_luks_volume(_DEFAULT_USB_DEVICE_ONE_PART)

        assert result.encryption is EncryptionScheme.LUKS
        assert not result.unlocked

    @mock.patch(
        "subprocess.check_output",
        side_effect=subprocess.CalledProcessError(1, "check_output"),
    )
    def test__get_luks_volume_error(self, mocked_subprocess):
        with pytest.raises(ExportException) as ex:
            self.cli._get_luks_volume(_DEFAULT_USB_DEVICE_ONE_PART)

        assert ex.value.sdstatus is Status.DEVICE_ERROR

    @mock.patch("os.path.exists", return_value=True)
    def test_unlock_luks_volume_success(self, mock_path, mocker):
        mock_popen = mocker.MagicMock()
        mock_popen_communicate = mocker.MagicMock()
        mock_popen.returncode = 0
        mock_popen.return_value = (("stdout", "stderr"), 0)

        mocker.patch("subprocess.Popen", return_value=mock_popen)
        mocker.patch(
            "subprocess.Popen.communicate", return_value=mock_popen_communicate
        )

        mapped_name = "luks-id-123456"
        vol = Volume(
            device_name=_DEFAULT_USB_DEVICE,
            mapped_name=mapped_name,
            encryption=EncryptionScheme.LUKS,
        )
        key = "a_key&_!"
        result = self.cli.unlock_luks_volume(vol, key)
        assert result.unlocked

    @mock.patch("os.path.exists", return_value=True)
    def test_unlock_luks_volume_unknown(self, mocker):
        mock_popen = mocker.MagicMock()
        mock_popen.communicate = mocker.MagicMock()
        mock_popen.communicate.returncode = 1  # An error unlocking

        mocker.patch("subprocess.Popen", mock_popen)

        vol = Volume(
            device_name=_DEFAULT_USB_DEVICE,
            mapped_name=_PRETEND_LUKS_ID,
            encryption=EncryptionScheme.UNKNOWN,
        )
        key = "a key!"

        with pytest.raises(ExportException) as ex:
            self.cli.unlock_luks_volume(vol, key)

        assert ex.value.sdstatus is Status.DEVICE_ERROR

    def test_unlock_luks_volume_passphrase_failure(self, mocker):
        mock_popen = mocker.MagicMock()
        mock_popen.communicate = mocker.MagicMock()
        mock_popen.communicate.returncode = 1  # An error unlocking

        mocker.patch("subprocess.Popen", mock_popen)

        vol = Volume(
            device_name=_DEFAULT_USB_DEVICE,
            mapped_name=_PRETEND_LUKS_ID,
            encryption=EncryptionScheme.LUKS,
        )
        key = "a key!"

        with pytest.raises(ExportException):
            self.cli.unlock_luks_volume(vol, key)

    @mock.patch(
        "subprocess.Popen", side_effect=subprocess.CalledProcessError(1, "Popen")
    )
    def test_unlock_luks_volume_luksOpen_exception(self, mocked_subprocess):
        pd = Volume(
            device_name=_DEFAULT_USB_DEVICE,
            mapped_name=_PRETEND_LUKS_ID,
            encryption=EncryptionScheme.LUKS,
        )
        key = "a key!"

        with pytest.raises(ExportException) as ex:
            self.cli.unlock_luks_volume(pd, key)

        assert ex.value.sdstatus is Status.DEVICE_ERROR

    @mock.patch("os.path.exists", return_value=True)
    @mock.patch(
        "subprocess.check_output", return_value=b"/dev/pretend/luks-id-123456\n"
    )
    @mock.patch("subprocess.check_call", return_value=0)
    def test_mount_volume_already_mounted(
        self, mocked_output, mocked_call, mocked_path
    ):
        md = Volume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            encryption=EncryptionScheme.LUKS,
        )
        result = self.cli.mount_volume(md)
        assert result.mountpoint == "/dev/pretend/luks-id-123456"
        assert isinstance(result, MountedVolume)

    @mock.patch("os.path.exists", return_value=True)
    @mock.patch("subprocess.check_output", return_value=b"\n")
    @mock.patch("subprocess.check_call", return_value=0)
    def test_mount_volume_mkdir(self, mocked_output, mocked_subprocess, mocked_path):
        md = Volume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            encryption=EncryptionScheme.LUKS,
        )
        mv = self.cli.mount_volume(md)
        assert mv.mapped_name == _PRETEND_LUKS_ID
        assert isinstance(mv, MountedVolume)

    @mock.patch("subprocess.check_output", return_value=b"\n")
    @mock.patch(
        "subprocess.check_call",
        side_effect=subprocess.CalledProcessError(1, "check_call"),
    )
    def test_mount_volume_error(self, mocked_subprocess, mocked_output):
        md = Volume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            encryption=EncryptionScheme.LUKS,
        )

        with pytest.raises(ExportException) as ex:
            self.cli.mount_volume(md)

        assert ex.value.sdstatus is Status.ERROR_MOUNT

    @mock.patch("os.path.exists", return_value=True)
    @mock.patch("subprocess.check_call", return_value=0)
    def test__unmount_volume(self, mocked_subprocess, mocked_mountpath):
        mounted = MountedVolume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            mountpoint="/media/usb",
            encryption=EncryptionScheme.LUKS,
        )

        result = self.cli._unmount_volume(mounted)
        assert not isinstance(result, MountedVolume)

    @mock.patch("os.path.exists", return_value=True)
    @mock.patch(
        "subprocess.check_call",
        side_effect=subprocess.CalledProcessError(1, "check_call"),
    )
    def test__unmount_volume_error(self, mocked_subprocess, mocked_mountpath):
        mounted = MountedVolume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            mountpoint=_EXAMPLE_MOUNTPOINT,
            encryption=EncryptionScheme.LUKS,
        )

        with pytest.raises(ExportException) as ex:
            self.cli._unmount_volume(mounted)

        assert ex.value.sdstatus is Status.DEVICE_ERROR

    @mock.patch("os.path.exists", return_value=True)
    @mock.patch("subprocess.check_call", return_value=0)
    def test__close_luks_volume(self, mocked_subprocess, mocked_os_call):
        mapped = Volume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            encryption=EncryptionScheme.LUKS,
        )

        # If call completes without error, drive was successfully closed with luksClose
        self.cli._close_luks_volume(mapped)

    @mock.patch("os.path.exists", return_value=True)
    @mock.patch(
        "subprocess.check_call",
        side_effect=subprocess.CalledProcessError(1, "check_call"),
    )
    def test__close_luks_volume_error(self, mocked_subprocess, mocked_os_call):
        mapped = Volume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            encryption=EncryptionScheme.LUKS,
        )

        with pytest.raises(ExportException) as ex:
            self.cli._close_luks_volume(mapped)

        assert ex.value.sdstatus is Status.DEVICE_ERROR

    @mock.patch(
        "subprocess.check_call",
        side_effect=subprocess.CalledProcessError(1, "check_call"),
    )
    def test__remove_temp_directory_error(self, mocked_subprocess):
        with pytest.raises(ExportException):
            self.cli._remove_temp_directory("tmp")

    @mock.patch("subprocess.check_call", return_value=0)
    def test_write_to_disk(self, mock_check_call):
        # Temporarily patch a method, to later assert it is called
        patch = mock.patch.object(self.cli, "cleanup_drive_and_tmpdir")
        patch.return_value = mock.MagicMock()
        patch.start()

        vol = MountedVolume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            mountpoint=_EXAMPLE_MOUNTPOINT,
            encryption=EncryptionScheme.LUKS,
        )

        submission = Archive("testfile")

        self.cli.write_data_to_device(submission.tmpdir, submission.target_dirname, vol)
        self.cli.cleanup_drive_and_tmpdir.assert_called_once()

        # Don't want to patch it indefinitely though, that will mess with the other tests
        patch.stop()

    @mock.patch(
        "subprocess.check_call",
        side_effect=subprocess.CalledProcessError(1, "check_call"),
    )
    def test_write_to_disk_error_still_does_cleanup(self, mock_call):
        # see above - patch internal method only for this test
        patch = mock.patch.object(self.cli, "cleanup_drive_and_tmpdir")
        patch.return_value = mock.MagicMock()
        patch.start()

        vol = MountedVolume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            mountpoint=_EXAMPLE_MOUNTPOINT,
            encryption=EncryptionScheme.LUKS,
        )
        submission = Archive("testfile")

        with pytest.raises(ExportException):
            self.cli.write_data_to_device(
                submission.tmpdir, submission.target_dirname, vol
            )
            self.cli.cleanup_drive_and_tmpdir.assert_called_once()

        patch.stop()

    @mock.patch(
        "subprocess.check_call",
        side_effect=subprocess.CalledProcessError(1, "check_call"),
    )
    def test_cleanup_drive_and_tmpdir_error(self, mocked_subprocess):
        submission = Archive("testfile")
        mock_volume = mock.MagicMock(Volume)

        with pytest.raises(ExportException) as ex:
            self.cli.cleanup_drive_and_tmpdir(mock_volume, submission.tmpdir)
        assert ex.value.sdstatus is Status.ERROR_EXPORT_CLEANUP

    @mock.patch("os.path.exists", return_value=False)
    @mock.patch("subprocess.check_call", return_value=0)
    def test_cleanup_drive_and_tmpdir(self, mock_subprocess, mocked_path):
        submission = Archive("testfile")
        vol = Volume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            encryption=EncryptionScheme.LUKS,
        )
        mv = MountedVolume.from_volume(vol, mountpoint=_EXAMPLE_MOUNTPOINT)

        close_patch = mock.patch.object(self.cli, "_close_luks_volume")
        remove_tmpdir_patch = mock.patch.object(self.cli, "_remove_temp_directory")

        close_mock = close_patch.start()
        rm_tpdir_mock = remove_tmpdir_patch.start()

        # That was all setup. Here's our test
        self.cli.cleanup_drive_and_tmpdir(mv, submission.tmpdir)

        close_mock.assert_called_once()
        rm_tpdir_mock.assert_called_once_with(submission.tmpdir)

        # Undo patch changes
        close_patch.stop()
        remove_tmpdir_patch.stop()

    @mock.patch(
        "subprocess.check_output",
        side_effect=subprocess.CalledProcessError(1, "check_output"),
    )
    def test_mountpoint_error(self, mock_subprocess):
        with pytest.raises(ExportException) as ex:
            self.cli._get_mountpoint(
                Volume(
                    device_name=_DEFAULT_USB_DEVICE,
                    mapped_name=_PRETEND_LUKS_ID,
                    encryption=EncryptionScheme.LUKS,
                )
            )

        assert ex.value.sdstatus is Status.ERROR_MOUNT

    @mock.patch("os.path.exists", return_value=False)
    def test_mount_mkdir_fails(self, mocked_path):
        mock_mountpoint = mock.patch.object(self.cli, "_get_mountpoint")
        mock_mountpoint.return_value = None

        vol = Volume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            encryption=EncryptionScheme.LUKS,
        )
        mock.patch.object(vol, "unlocked", return_value=True)

        with pytest.raises(ExportException) as ex:
            self.cli.mount_volume(vol)

        assert ex.value.sdstatus is Status.ERROR_MOUNT

    def test_mount_fails_with_locked_device(self):
        vol = Volume(
            device_name=_DEFAULT_USB_DEVICE_ONE_PART,
            mapped_name=_PRETEND_LUKS_ID,
            encryption=EncryptionScheme.LUKS,
        )
        mock.patch.object(vol, "unlocked", return_value=False)

        with pytest.raises(ExportException) as ex:
            self.cli.mount_volume(vol)

        assert ex.value.sdstatus == Status.ERROR_MOUNT

    @mock.patch("os.path.exists", return_value=True)
    @mock.patch(
        "subprocess.check_output",
        side_effect=[
            b"vc",
            _SAMPLE_CRYPTSETUP_STATUS_OUTPUT,
            _SAMPLE_MOUNTED_VC_OUTPUT,
        ],
    )
    def test_get_unlocked_veracrypt_mounted(self, mock_subprocess, mock_os):
        v = self.cli._attempt_get_unlocked_veracrypt_volume("/dev/sdc")

        assert v.unlocked
        assert v.mountpoint == _SAMPLE_MOUNTED_VC_OUTPUT.decode("utf-8")

    @mock.patch("os.path.exists", return_value=True)
    @mock.patch(
        "subprocess.check_output",
        side_effect=subprocess.CalledProcessError(1, "Oh no!"),
    )
    def test_get_unlocked_veracrypt_lsblk_error(self, mock_subprocess, mock_os):
        with pytest.raises(ExportException) as ex:
            self.cli._attempt_get_unlocked_veracrypt_volume("/dev/sdc")

        assert ex.value.sdstatus == Status.DEVICE_ERROR

    @mock.patch("os.path.exists", return_value=True)
    @mock.patch("subprocess.check_output", return_value=b"sdc disk\n")
    def test_get_unlocked_veracrypt_no_vc_drive(self, mock_subprocess, mock_os):
        with pytest.raises(ExportException) as ex:
            self.cli._attempt_get_unlocked_veracrypt_volume("/dev/sdc")

        assert ex.value.sdstatus == Status.UNKNOWN_DEVICE_DETECTED

    @mock.patch("os.path.exists", return_value=True)
    @mock.patch("subprocess.check_output", return_value=b"\n")
    def test_get_unlocked_veracrypt_empty_lsblk_error(self, mock_subprocess, mock_os):
        with pytest.raises(ExportException) as ex:
            self.cli._attempt_get_unlocked_veracrypt_volume("/dev/sdc")

        assert ex.value.sdstatus == Status.UNKNOWN_DEVICE_DETECTED
