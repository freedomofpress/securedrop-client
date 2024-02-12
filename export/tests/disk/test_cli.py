import pytest
from unittest import mock

import subprocess
import re

from securedrop_export.disk.cli import CLI
from securedrop_export.disk.volume import EncryptionScheme, Volume, MountedVolume
from securedrop_export.exceptions import ExportException
from securedrop_export.disk.status import Status

from securedrop_export.archive import Archive

# Sample lsblk and udisk inputs for testing the parsing of different device conditions
from ..lsblk_sample import (
    UDISKS_STATUS_MULTI_CONNECTED,
    UDISKS_STATUS_ONE_DEVICE_CONNECTED,
    UDISKS_STATUS_NOTHING_CONNECTED,
    ONE_DEVICE_LUKS_UNMOUNTED,
    ONE_DEVICE_VC_UNLOCKED,
    ERROR_ONE_DEVICE_LUKS_MOUNTED_MULTI_UNKNOWN_AVAILABLE,
    ERROR_NO_SUPPORTED_DEVICE,
    ERROR_UNENCRYPTED_DEVICE_MOUNTED,
    ERROR_DEVICE_MULTI_ENC_PARTITION,
    SINGLE_DEVICE_LOCKED,
    SINGLE_PART_LUKS_WRITABLE,
    SINGLE_PART_LUKS_UNLOCKED_UNMOUNTED,
    SINGLE_PART_UNLOCKED_VC_UNMOUNTED,
    SINGLE_DEVICE_ERROR_PARTITIONS_TOO_NESTED,
    SINGLE_DEVICE_ERROR_MOUNTED_PARTITION_NOT_ENCRYPTED,
    SINGLE_PART_VC_WRITABLE,
)

_PRETEND_LUKS_ID = "/dev/mapper/luks-dbfb85f2-77c4-4b1f-99a9-2dd3c6789094"
_PRETEND_VC = "/dev/mapper/tcrypt-2049"
_DEFAULT_USB_DEVICE = "/dev/sda"


# Lists for test paramaterization

supported_volumes_no_mount_required = [
    SINGLE_DEVICE_LOCKED,
    SINGLE_PART_LUKS_WRITABLE,
    SINGLE_PART_VC_WRITABLE,
]

# Volume, expected device name, expected mapped device name
# (used to mount)
supported_volumes_mount_required = [
    (SINGLE_PART_UNLOCKED_VC_UNMOUNTED, "/dev/sda1", "/dev/mapper/tcrypt-2049"),
    (
        SINGLE_PART_LUKS_UNLOCKED_UNMOUNTED,
        "/dev/sda1",
        "/dev/mapper/luks-dbfb85f2-77c4-4b1f-99a9-2dd3c6789094",
    ),
]

unsupported_volumes = [
    SINGLE_DEVICE_ERROR_MOUNTED_PARTITION_NOT_ENCRYPTED,
    SINGLE_DEVICE_ERROR_PARTITIONS_TOO_NESTED,
]


class TestCli:
    """
    Test the CLI wrapper that handless identification and locking/unlocking of
    USB volumes.

    This class is a wrapper around commandline tools like udsisks and lsblk,
    so a lot of the testing involves supplying sample input and ensuring it
    is parsed correctly (see `lsblk_sample.py`).
    """

    @classmethod
    def setup_class(cls):
        cls.cli = CLI()

    @classmethod
    def teardown_class(cls):
        cls.cli = None

    @mock.patch("subprocess.check_output")
    def test_get_volume_no_devices(self, mock_sp):
        mock_sp.side_effect = [
            UDISKS_STATUS_NOTHING_CONNECTED,
            ERROR_NO_SUPPORTED_DEVICE,
        ]

        with pytest.raises(ExportException) as ex:
            self.cli.get_volume()
        assert ex.value.sdstatus == Status.NO_DEVICE_DETECTED

    @mock.patch("securedrop_export.disk.cli.CLI._mount_volume")
    @mock.patch("subprocess.check_output")
    def test_get_volume_one_device(self, mock_sp, mock_mount):
        mock_sp.side_effect = [
            UDISKS_STATUS_ONE_DEVICE_CONNECTED,
            ONE_DEVICE_LUKS_UNMOUNTED,
        ]
        v = self.cli.get_volume()

        assert v.encryption == EncryptionScheme.LUKS
        # todo: list call args, make this test more specific

    @mock.patch("subprocess.check_output")
    def test_get_volume_multi_devices_error(self, mock_sp):
        mock_sp.side_effect = [
            UDISKS_STATUS_MULTI_CONNECTED,
            ERROR_ONE_DEVICE_LUKS_MOUNTED_MULTI_UNKNOWN_AVAILABLE,
        ]
        with pytest.raises(ExportException) as ex:
            self.cli.get_volume()

        assert ex.value.sdstatus == Status.MULTI_DEVICE_DETECTED

    @mock.patch("securedrop_export.disk.cli.CLI._mount_volume")
    @mock.patch("subprocess.check_output")
    def test_get_volume_too_many_encrypted_partitions(self, mock_sp, mock_mount):
        mock_sp.side_effect = [
            UDISKS_STATUS_ONE_DEVICE_CONNECTED,
            ERROR_DEVICE_MULTI_ENC_PARTITION,
        ]
        with pytest.raises(ExportException) as ex:
            self.cli.get_volume()

        assert ex.value.sdstatus == Status.INVALID_DEVICE_DETECTED

    @mock.patch("securedrop_export.disk.cli.CLI._get_supported_volume")
    @mock.patch("subprocess.check_output")
    def test_get_volume_no_encrypted_partition(self, mock_sp, mock_gsv):
        mock_sp.side_effect = [
            UDISKS_STATUS_ONE_DEVICE_CONNECTED,
            ERROR_UNENCRYPTED_DEVICE_MOUNTED,
        ]
        with pytest.raises(ExportException) as ex:
            self.cli.get_volume()

        assert ex.value.sdstatus == Status.INVALID_DEVICE_DETECTED

    @mock.patch("securedrop_export.disk.cli.CLI._get_supported_volume")
    @mock.patch("subprocess.check_output")
    def test_get_volume_empty_udisks_does_not_keep_checking(self, mock_sp, mock_gsv):
        mock_sp.side_effect = [
            UDISKS_STATUS_NOTHING_CONNECTED,
            ONE_DEVICE_VC_UNLOCKED,
        ]

        # If udisks2 didn't find it, don't keep looking
        with pytest.raises(ExportException) as ex:
            self.cli.get_volume()

        assert ex.value.sdstatus == Status.NO_DEVICE_DETECTED
        mock_gsv.assert_not_called()

    @pytest.mark.parametrize("input", supported_volumes_no_mount_required)
    def test__get_supported_volume_success_no_mount(self, input):
        vol = self.cli._get_supported_volume(input)

        assert vol

    @mock.patch("subprocess.check_output")
    def test__get_supported_volume_locked_success(self, mock_subprocess):
        vol = self.cli._get_supported_volume(SINGLE_DEVICE_LOCKED)
        assert vol.device_name == "/dev/sda"

    @pytest.mark.parametrize(
        "input,expected_device,expected_devmapper", supported_volumes_mount_required
    )
    @mock.patch("securedrop_export.disk.cli.CLI._mount_volume")
    @mock.patch(
        "securedrop_export.disk.cli.CLI._is_it_veracrypt",
        return_value=EncryptionScheme.VERACRYPT,
    )
    def test__get_supported_volume_requires_mounting(
        self, mock_v, mock_mount, input, expected_device, expected_devmapper
    ):
        self.cli._get_supported_volume(input)

        mock_mount.assert_called_once()

        assert mock_mount.call_args_list[0][0][0].device_name == expected_device
        assert mock_mount.call_args_list[0][0][1] == expected_devmapper

    @pytest.mark.parametrize("input", unsupported_volumes)
    @mock.patch("securedrop_export.disk.cli.CLI._mount_volume")
    def test__get_supported_volume_none_supported(self, mock_subprocess, input):
        result = self.cli._get_supported_volume(input)

        assert result is None

    @mock.patch("pexpect.spawn")
    def test_unlock_success(self, mock_p):
        child = mock_p()
        vol = Volume(_DEFAULT_USB_DEVICE, EncryptionScheme.LUKS)

        # This return value is derived from the "expected" list in the
        # unlock_volume method (list item with index 0 is success)
        child.expect.side_effect = [0, 0]
        child.match = mock.MagicMock(spec=re.Match)
        child.match.group.return_value = "/dev/dm-0".encode("utf-8")

        mv = mock.MagicMock(spec=MountedVolume)

        with mock.patch.object(self.cli, "_mount_volume") as mock_mount:
            mock_mount.return_value = mv
            result = self.cli.unlock_volume(vol, "a passw0rd!")

            mock_mount.assert_called_once_with(vol, "/dev/dm-0")
            assert isinstance(result, MountedVolume)

    @mock.patch("pexpect.spawn")
    def test_unlock_already_unlocked(self, mock_p):
        vol = Volume(_DEFAULT_USB_DEVICE, EncryptionScheme.LUKS)
        child = mock_p()
        child.expect.side_effect = [0, 1]
        child.match = mock.MagicMock(spec=re.Match)
        error_msg = "/dev/dm-0".encode("utf-8")
        child.match.group.return_value = error_msg
        mv = mock.MagicMock(spec=MountedVolume)

        with mock.patch.object(self.cli, "_mount_volume") as mock_mount:
            mock_mount.return_value = mv
            result = self.cli.unlock_volume(vol, "a passw0rd!")

        mock_mount.assert_called_once_with(vol, "/dev/dm-0")
        assert isinstance(result, MountedVolume)

    @mock.patch("pexpect.spawn")
    def test_unlock_remote_fail(self, mock_p):
        child = mock_p()
        child.expect.return_value = 3
        vol = Volume(_DEFAULT_USB_DEVICE, EncryptionScheme.LUKS)

        with pytest.raises(ExportException) as ex:
            self.cli.unlock_volume(vol, "a passw0rd!")

        assert ex.value.sdstatus == Status.ERROR_UNLOCK_GENERIC

    @mock.patch("pexpect.spawn")
    def test_unlock_luks_bad_passphrase(self, mock_p):
        child = mock_p()

        # This return value is derived from the "expected" list in the
        # unlock_volume method (list item with index 1 is the "Bad passphrase"
        # error)
        child.expect.side_effect = [0, 2]
        child.match = mock.MagicMock(spec=re.Match)
        child.match.group.return_value = b"/media/usb"

        vol = Volume(_DEFAULT_USB_DEVICE, EncryptionScheme.LUKS)

        with pytest.raises(ExportException) as ex:
            self.cli.unlock_volume(vol, "a mistaken p4ssw0rd!")

        assert ex.value.sdstatus == Status.ERROR_UNLOCK_LUKS

    @mock.patch("pexpect.spawn")
    def test_unlock_fail(self, mock_p):
        child = mock_p()

        # This is derived from the "expected" list in the unlock_volume method
        # (list item with index 3 is the "pexpect.EOF" error)
        child.expect.side_effect = [0, 3]
        child.match = mock.MagicMock(spec=re.Match)
        child.match.group.return_value = b"/media/usb"

        vol = Volume(_DEFAULT_USB_DEVICE, EncryptionScheme.LUKS)

        with pytest.raises(ExportException) as ex:
            self.cli.unlock_volume(vol, "a passw0rd!")

        assert ex.value.sdstatus == Status.ERROR_UNLOCK_GENERIC

    @mock.patch("pexpect.spawn")
    def test__mount_volume_already_mounted(self, mock_p):
        child = mock_p()
        child.expect.return_value = 1
        child.match = mock.MagicMock(spec=re.Match)
        child.match.group.return_value = b"/media/usb"

        md = MountedVolume(
            device_name=_DEFAULT_USB_DEVICE,
            unlocked_name=_PRETEND_LUKS_ID,
            encryption=EncryptionScheme.LUKS,
            mountpoint="/media/usb",
        )
        result = self.cli._mount_volume(md, _PRETEND_LUKS_ID)

        assert result.mountpoint == "/media/usb"
        assert isinstance(result, MountedVolume)

    @mock.patch("pexpect.spawn")
    def test__mount_volume_success(self, mock_p):
        child = mock_p()
        child.expect.return_value = 0
        child.match = mock.MagicMock(spec=re.Match)
        child.match.group.return_value = b"/media/usb"

        md = MountedVolume(
            device_name=_DEFAULT_USB_DEVICE,
            unlocked_name=_PRETEND_LUKS_ID,
            encryption=EncryptionScheme.LUKS,
            mountpoint="/media/usb",
        )

        result = self.cli._mount_volume(md, _PRETEND_LUKS_ID)

        assert result.mountpoint == "/media/usb"
        assert isinstance(result, MountedVolume)

    @mock.patch("pexpect.spawn")
    def test__mount_volume_error(self, mock_p):
        child = mock_p()
        child.expect.return_value = 2

        md = Volume(
            device_name="/dev/sda",
            encryption=EncryptionScheme.LUKS,
        )

        with pytest.raises(ExportException) as ex:
            self.cli._mount_volume(md, _PRETEND_LUKS_ID)

        assert ex.value.sdstatus is Status.ERROR_MOUNT

    @mock.patch("subprocess.check_call")
    def test__unmount_volume(self, mock_sp):
        mock_sp.returncode = 0
        mounted = MountedVolume(
            device_name="/dev/sda",
            unlocked_name=f"/dev/mapper{_PRETEND_LUKS_ID}",
            mountpoint="/media/usb",
            encryption=EncryptionScheme.LUKS,
        )

        result = self.cli._close_volume(mounted)
        assert not isinstance(result, MountedVolume)

    @mock.patch("subprocess.check_call", return_value=0)
    def test_write_to_disk(self, mock_check_call):
        # Temporarily patch a method, to later assert it is called
        patch = mock.patch.object(self.cli, "cleanup")
        patch.return_value = mock.MagicMock()
        patch.start()

        vol = MountedVolume(
            device_name=_DEFAULT_USB_DEVICE,
            unlocked_name=_PRETEND_LUKS_ID,
            mountpoint="/media/usb",
            encryption=EncryptionScheme.LUKS,
        )

        submission = Archive("testfile")

        self.cli.write_data_to_device(vol, submission.tmpdir, submission.target_dirname)
        self.cli.cleanup.assert_called_once()

        # Don't want to patch it indefinitely though, that will mess with the other tests
        patch.stop()

    @mock.patch(
        "subprocess.check_call",
        side_effect=subprocess.CalledProcessError(1, "check_call"),
    )
    def test_write_to_disk_error_still_does_cleanup(self, mock_call):
        # patch internal method only for this test
        patch = mock.patch.object(self.cli, "cleanup")
        patch.return_value = mock.MagicMock()
        patch.start()

        vol = MountedVolume(
            device_name=_DEFAULT_USB_DEVICE,
            unlocked_name=_PRETEND_LUKS_ID,
            mountpoint="/media/usb",
            encryption=EncryptionScheme.LUKS,
        )
        submission = Archive("testfile")

        with pytest.raises(ExportException):
            self.cli.write_data_to_device(
                vol, submission.tmpdir, submission.target_dirname
            )
            self.cli.cleanup.assert_called_once()

        patch.stop()

    @mock.patch(
        "subprocess.check_call",
        side_effect=subprocess.CalledProcessError(1, "check_call"),
    )
    def test_cleanup_error(self, mock_popen):
        submission = Archive("testfile")
        mock_volume = mock.MagicMock(Volume)

        with pytest.raises(ExportException) as ex:
            self.cli.cleanup(mock_volume, submission.tmpdir)
        assert ex.value.sdstatus is Status.ERROR_EXPORT_CLEANUP

    @mock.patch(
        "subprocess.check_call",
        side_effect=subprocess.CalledProcessError(1, "check_call"),
    )
    def test_cleanup_error_reports_exporterror_if_flagged(self, mock_popen):
        submission = Archive("testfile")
        mock_volume = mock.MagicMock(Volume)

        with pytest.raises(ExportException) as ex:
            self.cli.cleanup(mock_volume, submission.tmpdir, is_error=True)
        assert ex.value.sdstatus is Status.ERROR_EXPORT

    @mock.patch("os.path.exists", return_value=False)
    @mock.patch("subprocess.check_call", return_value=0)
    def test_cleanup(self, mock_subprocess, mocked_path):
        submission = Archive("testfile")
        vol = Volume(
            device_name=_DEFAULT_USB_DEVICE,
            encryption=EncryptionScheme.LUKS,
        )
        mv = MountedVolume(
            vol.device_name,
            f"/dev/mapper/{_PRETEND_LUKS_ID}",
            vol.encryption,
            mountpoint="/media/usb",
        )

        close_patch = mock.patch.object(self.cli, "_close_volume")
        remove_tmpdir_patch = mock.patch.object(self.cli, "_remove_temp_directory")
        close_mock = close_patch.start()
        rm_tpdir_mock = remove_tmpdir_patch.start()

        self.cli.cleanup(mv, submission.tmpdir)

        close_mock.assert_called_once()
        rm_tpdir_mock.assert_called_once_with(submission.tmpdir)

        # Undo patch changes
        close_patch.stop()
        remove_tmpdir_patch.stop()

    @mock.patch("pexpect.spawn")
    def test_parse_correct_mountpoint_from_pexpect(self, mock_pexpect):
        child = mock_pexpect()
        child.expect.return_value = 1
        child.match = mock.MagicMock()
        child.match.group.side_effect = [
            "/dev/dm-0".encode("utf-8"),
            "/media/usb".encode("utf-8"),
        ]

        mv = self.cli._mount_volume(
            Volume("/dev/sda1", EncryptionScheme.VERACRYPT), "/dev/mapper/vc"
        )
        assert mv.unlocked_name == "/dev/dm-0"
        assert mv.mountpoint == "/media/usb"
