from unittest import mock
import os
import tempfile

from securedrop_export.exceptions import ExportException
from securedrop_export.disk.status import Status
from securedrop_export.disk.volume import Volume, MountedVolume, EncryptionScheme
from securedrop_export.archive import Archive, Metadata
from securedrop_export.disk.service import Service
from securedrop_export.disk.cli import CLI

SAMPLE_OUTPUT_LSBLK_NO_PART = b"disk\ncrypt"  # noqa
SAMPLE_OUTPUT_USB = "/dev/sda"  # noqa
SAMPLE_OUTPUT_USB_PARTITIONED = "/dev/sda1"


class TestExportService:
    @classmethod
    def setup_class(cls):
        cls.mock_cli = mock.MagicMock(spec=CLI)
        cls.mock_submission = cls._setup_submission()

        cls.mock_luks_volume_unmounted = Volume(
            device_name=SAMPLE_OUTPUT_USB,
            mapped_name="fake-luks-id-123456",
            encryption=EncryptionScheme.LUKS,
        )
        cls.mock_luks_volume_mounted = MountedVolume(
            device_name=SAMPLE_OUTPUT_USB,
            mapped_name="fake-luks-id-123456",
            mountpoint="/media/usb",
            encryption=EncryptionScheme.LUKS,
        )

        cls.mock_vc_volume_mounted = MountedVolume(
            device_name=SAMPLE_OUTPUT_USB,
            mapped_name="mock-veracrypt-vol",
            encryption=EncryptionScheme.VERACRYPT,
            mountpoint="/media/usb/",
        )

        cls.mock_vc_volume_unmounted = Volume(
            device_name=SAMPLE_OUTPUT_USB,
            mapped_name=None,
            encryption=EncryptionScheme.UNKNOWN,
        )

        cls.service = Service(cls.mock_submission, cls.mock_cli)

    @classmethod
    def teardown_class(cls):
        cls.mock_cli = None
        cls.mock_submission = None
        cls.service = None

    @classmethod
    def _setup_submission(cls) -> Archive:
        """
        Helper method to set up sample archive
        """
        submission = Archive("testfile")
        temp_folder = tempfile.mkdtemp()
        metadata = os.path.join(temp_folder, Metadata.METADATA_FILE)
        with open(metadata, "w") as f:
            f.write(
                '{"device": "disk", "encryption_method":'
                ' "luks", "encryption_key": "hunter1"}'
            )

        return submission.set_metadata(Metadata(temp_folder).validate())

    def setup_method(self, method):
        """
        By default, mock CLI will return the "happy path" of a correctly-formatted LUKS drive.
        Override this behaviour in the target method as required, for example to simulate CLI
        errors. `teardown_method()` will reset the side effects so they do not affect subsequent
        test methods.
        """
        self.mock_cli._get_luks_volume.return_value = self.mock_luks_volume_unmounted
        self.mock_cli.mount_volume.return_value = self.mock_luks_volume_mounted
        self.mock_cli.get_all_volumes.return_value = [self.mock_luks_volume_unmounted]

    def teardown_method(self, method):
        self.mock_cli.reset_mock(return_value=True, side_effect=True)

    def test_scan_all_device_is_locked_luks(self):
        status = self.service.scan_all_devices()

        assert status == Status.DEVICE_LOCKED

    def test_scan_all_no_devices_connected(self):
        self.mock_cli.get_all_volumes.return_value = []

        assert self.service.scan_all_devices() == Status.NO_DEVICE_DETECTED

    def test_scan_all_too_many_devices_connected(self):
        self.mock_cli.get_all_volumes.return_value = [
            SAMPLE_OUTPUT_USB,
            "/dev/sdb",
        ]

        assert self.service.scan_all_devices() == Status.MULTI_DEVICE_DETECTED

    def test_scan_all_devices_error(self):
        self.mock_cli.get_all_volumes.side_effect = ExportException("zounds!")

        assert self.service.scan_all_devices() == Status.DEVICE_ERROR

    def test_scan_all_device_is_not_luks_and_unlocked(self):
        self.mock_cli.get_all_volumes.return_value = [self.mock_vc_volume_mounted]

        assert self.service.scan_all_devices() == Status.DEVICE_WRITABLE

    def test_scan_all_device_is_not_luks_and_not_unlocked_error(self):
        self.mock_cli.get_all_volumes.return_value = [self.mock_vc_volume_unmounted]

        assert self.service.scan_all_devices() == Status.UNKNOWN_DEVICE_DETECTED

        self.mock_cli.get_all_volumes.side_effect = ExportException(
            sdstatus=Status.DEVICE_ERROR
        )

        assert self.service.scan_all_devices() == Status.DEVICE_ERROR

    def test_scan_all_device_is_locked_veracrypt_volume(self):
        self.mock_cli.get_all_volumes.return_value = [self.mock_vc_volume_unmounted]

        assert self.service.scan_all_devices() == Status.UNKNOWN_DEVICE_DETECTED

    def test_export_already_mounted_no_cleanup(self):
        self.mock_cli.get_all_volumes.return_value = [self.mock_luks_volume_mounted]
        mock_write = mock.MagicMock()
        self.mock_cli.write_data_to_device = mock_write
        result = self.service.export()

        assert result == Status.SUCCESS_EXPORT
        mock_write.assert_called_once_with(
            self.mock_submission.tmpdir,
            self.mock_submission.target_dirname,
            self.mock_luks_volume_mounted,
        )

    @mock.patch("os.path.exists", return_value=True)
    def test_export_write_error(self, mock_path):
        self.mock_cli.get_all_volumes.return_value = [self.mock_luks_volume_mounted]
        self.mock_cli.write_data_to_device.side_effect = ExportException(
            sdstatus=Status.ERROR_EXPORT
        )

        assert self.service.export() == Status.ERROR_EXPORT

    @mock.patch("os.path.exists", return_value=True)
    def test_export_unlock_error(self, mock_path):
        self.mock_cli.unlock_luks_volume.side_effect = ExportException("oh no!")

        assert self.service.export() == Status.ERROR_UNLOCK_LUKS
