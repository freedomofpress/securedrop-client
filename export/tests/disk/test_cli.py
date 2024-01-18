import pytest
from unittest import mock

import json

import subprocess

from securedrop_export.disk.cli import CLI
from securedrop_export.disk.volume import EncryptionScheme, Volume, MountedVolume
from securedrop_export.exceptions import ExportException
from securedrop_export.disk.status import Status

from securedrop_export.archive import Archive

import pdb  # TODO

# Mock lsblk output
from ..lsblk_sample import *

# Test data for parametrization
lsblk_supported = [
    (LSBLK_VALID_DEVICE_LOCKED, Volume("/dev/sda", EncryptionScheme.LUKS)),
    (
        LSBLK_VALID_DEVICE_WRITABLE,
        MountedVolume(
            "/dev/sda1",
            "luks-dbfb85f2-77c4-4b1f-99a9-2dd3c6789094",
            encryption=EncryptionScheme.LUKS,
            mountpoint="/media/usb",
        ),
    ),
    (
        LSBLK_VALID_MULTIPART_DEVICE_LOCKED_PLUS_INVALID_DEVICE_INSERTED,
        Volume("/dev/sda2", EncryptionScheme.LUKS),
    ),
]

lsblk_unsupported = [
    (LSBLK_ERROR_NO_DEVICE, Status.NO_DEVICE_DETECTED),
    # Only an error if both devices are suitable targets
    (LSBLK_ERROR_MULTI_DEVICE_INSERTED, Status.MULTI_DEVICE_DETECTED),
]

single_device_supported = [
    (SINGLE_DEVICE_LOCKED, Volume("/dev/sda", EncryptionScheme.LUKS)),
    (SINGLE_DEVICE_MULTIPART_LOCKED, Volume("/dev/sda2", EncryptionScheme.LUKS)),
    (
        SINGLE_DEVICE_WRITABLE,
        MountedVolume(
            "/dev/sda1",
            "luks-dbfb85f2-77c4-4b1f-99a9-2dd3c6789094",
            encryption=EncryptionScheme.LUKS,
            mountpoint="/media/usb",
        ),
    ),
    (
        SINGLE_DEVICE_UNLOCKED_VC_UNMOUNTED,
        MountedVolume(
            "/dev/sda1",
            "tcrypt-2049",
            EncryptionScheme.VERACRYPT,
            mountpoint="/media/usb",
        ),
    ),
    (
        SINGLE_DEVICE_WRITABLE_SECOND_PART,
        MountedVolume(
            "/dev/sda2",
            "luks-dbfb85f2-77c4-4b1f-99a9-2dd3c6789094",
            EncryptionScheme.LUKS,
            mountpoint="/media/usb",
        ),
    ),
]

single_device_unsupported = [
    SINGLE_DEVICE_ERROR_MULTI_ENC_PARTITION,
    SINGLE_DEVICE_ERROR_PARTITIONS_TOO_NESTED,
    SINGLE_DEVICE_ERROR_MOUNTED_PARTITION_NOT_ENCRYPTED,
]

_PRETEND_LUKS_ID = "luks-dbfb85f2-77c4-4b1f-99a9-2dd3c6789094"
_PRETEND_VC = "tcrypt-2049"
_DEFAULT_USB_DEVICE = "/dev/sda"


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

    @mock.patch("securedrop_export.disk.cli.CLI._parse_single_device")
    @mock.patch("subprocess.check_output")
    def test_get_volume2(self, mock_sp, mock_parse):
        mock_sp.return_value = LSBLK_VALID_DEVICE_LOCKED
        self.cli.get_volume()

        mock_parse.assert_called()

    @pytest.mark.parametrize("lsblk,expected", lsblk_supported)
    @mock.patch("subprocess.check_output")
    def test_get_volume(self, mock_subprocess, lsblk, expected):
        mock_subprocess.return_value = lsblk

        with mock.patch.object(
            self.cli, "_parse_single_device", wraps="_parse_single_device"
        ) as patch_parse, mock.patch.object(
            self.cli, "_get_supported_volume", wraps="_get_supported_volume"
        ) as patch_gsv:
            patch_parse.return_value = expected
            v = self.cli.get_volume()

    @pytest.mark.parametrize("output,expected", lsblk_unsupported)
    @mock.patch("subprocess.check_output")
    def test_get_volume_fail(self, mock_subprocess, output, expected):
        mock_subprocess.return_value = output

        with mock.patch.object(self.cli, "_parse_single_device"), pytest.raises(
            ExportException
        ) as ex:
            self.cli.get_volume()

        assert ex.value.sdstatus == expected

    @pytest.mark.parametrize("input,expected", single_device_supported)
    @mock.patch("subprocess.getstatusoutput", returncode=0)
    @mock.patch("subprocess.check_output")
    @mock.patch("securedrop_export.disk.cli.CLI._mount_volume")
    def test__parse_single_device_success(
        self, mock_mount, mock_status_output, mock_subprocess, input, expected
    ):
        mock_subprocess.returncode = 0
        mock_subprocess.return_value = "/media/usb"  # pretend mountpoint
        mock_status_output.returncode = 0

        vol = self.cli._parse_single_device(input)

        assert vol

    @mock.patch("subprocess.check_output")
    def test__parse_single_device_locked_success(self, mock_subprocess):
        vol = self.cli._parse_single_device(SINGLE_DEVICE_LOCKED)
        assert vol.device_name == "sda"

    @pytest.mark.parametrize("input", single_device_unsupported)
    def test__parse_single_device_fail(self, input):
        with pytest.raises(ExportException) as ex:
            self.cli._parse_single_device(input)

        assert ex.value.sdstatus == Status.INVALID_DEVICE_DETECTED

    def test_unlock_success(self, mocker):
        mock_popen = mocker.MagicMock()
        mock_communicate = mocker.MagicMock()
        mock_popen.returncode = 0  # Successful unlock

        mocker.patch("subprocess.Popen", return_value=mock_popen)
        mocker.patch("subprocess.Popen.communicate", return_value=mock_communicate)

        mv = mock.MagicMock(spec=MountedVolume)
        vol = Volume(_DEFAULT_USB_DEVICE, EncryptionScheme.LUKS)

        with mock.patch.object(
            self.cli, "_get_mapped_name"
        ) as mock_mapped_name, mock.patch.object(
            self.cli, "_mount_volume"
        ) as mock_mount:
            mock_mapped_name.return_value = _PRETEND_LUKS_ID
            mock_mount.return_value = mv
            result = self.cli.unlock_volume(vol, "a passw0rd!")

        assert isinstance(result, MountedVolume)

    def test_unlock_already_unlocked(self, mocker):
        mock_popen = mocker.MagicMock()
        mock_communicate = mocker.MagicMock()
        mock_popen.returncode = 1  # udisks2 already unlocked

        mocker.patch("subprocess.Popen", return_value=mock_popen)
        mocker.patch("subprocess.Popen.communicate", return_value=mock_communicate)

        mv = mock.MagicMock(spec=MountedVolume)
        vol = Volume(_DEFAULT_USB_DEVICE, EncryptionScheme.LUKS)

        with mock.patch.object(
            self.cli, "_get_mapped_name"
        ) as mock_map, mock.patch.object(self.cli, "_mount_volume") as mock_mount:
            mock_map.return_value = _PRETEND_LUKS_ID
            mock_mount.return_value = mv
            result = self.cli.unlock_volume(vol, "a passw0rd!")

        mock_map.assert_called_once()
        mock_mount.assert_called_once_with(vol, _PRETEND_LUKS_ID)
        assert isinstance(result, MountedVolume)

    def test_unlock_devmapper_fail(self, mocker):
        mock_popen = mocker.MagicMock()
        mock_communicate = mocker.MagicMock()
        mock_popen.returncode = 1  # udisks2 already unlocked

        mocker.patch("subprocess.Popen", return_value=mock_popen)
        mocker.patch("subprocess.Popen.communicate", return_value=mock_communicate)

        mv = mock.MagicMock(spec=MountedVolume)
        vol = Volume(_DEFAULT_USB_DEVICE, EncryptionScheme.LUKS)

        mock_mapped_name = mock.patch.object(
            self.cli, "_get_mapped_name", return_value=None
        )
        mock_mapped_name.start()

        with pytest.raises(ExportException) as ex:
            self.cli.unlock_volume(vol, "a passw0rd!")

        assert ex.value.sdstatus == Status.ERROR_UNLOCK_GENERIC
        mock_mapped_name.stop()

    @mock.patch(
        "subprocess.Popen", side_effect=subprocess.CalledProcessError(4, "Popen")
    )
    def test_unlock_fail(self, mock_popen):
        vol = Volume(_DEFAULT_USB_DEVICE, EncryptionScheme.LUKS)

        with pytest.raises(ExportException) as ex:
            self.cli.unlock_volume(vol, "a mistaken p4ssw0rd!")

        assert ex.value.sdstatus == Status.ERROR_UNLOCK_LUKS

    def test_unlock_luks_volume_bad_passphrase(self, mocker):
        mock_popen = mocker.MagicMock()
        mock_communicate = mocker.MagicMock()
        mock_popen.returncode = 2  # Error unlocking

        mocker.patch("subprocess.Popen", return_value=mock_popen)
        mocker.patch("subprocess.Popen.communicate", return_value=mock_communicate)

        vol = Volume(_DEFAULT_USB_DEVICE, EncryptionScheme.LUKS)

        with pytest.raises(ExportException) as ex:
            self.cli.unlock_volume(vol, "a passw0rd!")

        assert ex.value.sdstatus == Status.ERROR_UNLOCK_LUKS

    @mock.patch(
        "subprocess.Popen", side_effect=subprocess.CalledProcessError(5, "Popen")
    )
    def test_unlock_luks_volume_exception(self, mocked_subprocess_popen):
        vol = Volume(
            device_name=_DEFAULT_USB_DEVICE,
            encryption=EncryptionScheme.LUKS,
        )
        key = "a key!"

        with pytest.raises(ExportException) as ex:
            self.cli.unlock_volume(vol, key)

        assert ex.value.sdstatus is Status.ERROR_UNLOCK_LUKS

    @mock.patch("subprocess.check_output")
    @mock.patch("subprocess.getstatusoutput", return_value=(0, b"AlreadyMounted"))
    def test__mount_volume_already_mounted(
        self, mocked_statusoutput, mocked_subprocess
    ):
        mocked_subprocess.return_value = b"/media/usb"
        md = Volume(
            device_name=_DEFAULT_USB_DEVICE,
            encryption=EncryptionScheme.LUKS,
        )
        result = self.cli._mount_volume(md, _PRETEND_LUKS_ID)
        assert result.mountpoint == "/media/usb"
        assert isinstance(result, MountedVolume)

    @mock.patch(
        "subprocess.getstatusoutput",
        side_effect=subprocess.CalledProcessError(1, "Oh no"),
    )
    def test__mount_volume_error(self, mock_getstatusoutput):
        md = Volume(
            device_name="/dev/sda",
            encryption=EncryptionScheme.LUKS,
        )

        with pytest.raises(ExportException) as ex:
            self.cli._mount_volume(md, _PRETEND_LUKS_ID)

        assert ex.value.sdstatus is Status.ERROR_MOUNT

    def test_write_to_disk(self):
        pass

    def test_write_to_disk_error(self):
        pass

    def test_cleanup(self):
        pass

    def test_cleanup_error_device_busy(self):
        pass

    def test_cleanup_error_generic(self):
        pass

    def test__unmount_volume(self):
        mounted = MountedVolume(
            device_name="/dev/sda",
            mapped_name=_PRETEND_LUKS_ID,
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
            mapped_name=_PRETEND_LUKS_ID,
            mountpoint="/media/usb",
            encryption=EncryptionScheme.LUKS,
        )

        submission = Archive("testfile")

        self.cli.write_data_to_device(submission.tmpdir, submission.target_dirname, vol)
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
            mapped_name=_PRETEND_LUKS_ID,
            mountpoint="/media/usb",
            encryption=EncryptionScheme.LUKS,
        )
        submission = Archive("testfile")

        with pytest.raises(ExportException):
            self.cli.write_data_to_device(
                submission.tmpdir, submission.target_dirname, vol
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

    @mock.patch("os.path.exists", return_value=False)
    @mock.patch("subprocess.check_call", return_value=0)
    def test_cleanup(self, mock_subprocess, mocked_path):
        submission = Archive("testfile")
        vol = Volume(
            device_name=_DEFAULT_USB_DEVICE,
            encryption=EncryptionScheme.LUKS,
        )
        mv = MountedVolume(
            vol.device_name, _PRETEND_LUKS_ID, vol.encryption, mountpoint="/media/usb"
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
