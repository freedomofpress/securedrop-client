import os
import tempfile
from unittest import mock

from securedrop_export.archive import Archive, Metadata
from securedrop_export.disk.cli import CLI
from securedrop_export.disk.service import Service
from securedrop_export.disk.status import Status
from securedrop_export.disk.volume import EncryptionScheme, MountedVolume, Volume
from securedrop_export.exceptions import ExportException

SAMPLE_OUTPUT_USB = "/dev/sda"
SAMPLE_OUTPUT_USB_PARTITIONED = "/dev/sda1"


class TestExportService:
    @classmethod
    def setup_class(cls):
        cls.mock_cli = mock.MagicMock(spec=CLI)
        cls.mock_submission = cls._setup_submission()

        cls.mock_luks_volume_unmounted = Volume(
            device_name=SAMPLE_OUTPUT_USB,
            encryption=EncryptionScheme.LUKS,
        )
        cls.mock_luks_volume_mounted = MountedVolume(
            device_name=SAMPLE_OUTPUT_USB,
            unlocked_name="/dev/mapper/fake-luks-id-123456",
            mountpoint="/media/usb",
            encryption=EncryptionScheme.LUKS,
        )

        cls.mock_vc_volume_mounted = MountedVolume(
            device_name=SAMPLE_OUTPUT_USB,
            unlocked_name="/dev/mapper/mock-veracrypt-vol",
            encryption=EncryptionScheme.VERACRYPT,
            mountpoint="/media/usb/",
        )

        cls.mock_vc_volume_locked = Volume(
            device_name=SAMPLE_OUTPUT_USB,
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
            f.write('{"device": "disk", "encryption_key": "hunter1"}')

        return submission.set_metadata(Metadata(temp_folder).validate())

    def setup_method(self, method):
        pass

    def teardown_method(self, method):
        self.mock_cli.reset_mock(return_value=True, side_effect=True)

    def test_scan_all_device_is_locked(self):
        self.mock_cli.get_volume.return_value = self.mock_luks_volume_unmounted
        status = self.service.scan_all_devices()

        assert status == Status.DEVICE_LOCKED

    def test_scan_all_no_devices_connected(self):
        self.mock_cli.get_volume.side_effect = ExportException(
            sdstatus=Status.NO_DEVICE_DETECTED
        )

        assert self.service.scan_all_devices() == Status.NO_DEVICE_DETECTED

    def test_scan_all_too_many_devices_connected(self):
        self.mock_cli.get_volume.side_effect = ExportException(
            sdstatus=Status.MULTI_DEVICE_DETECTED
        )

        assert self.service.scan_all_devices() == Status.MULTI_DEVICE_DETECTED

    def test_scan_all_devices_error(self):
        self.mock_cli.get_volume.side_effect = ExportException("zounds!")

        assert self.service.scan_all_devices() == Status.DEVICE_ERROR

    def test_scan_all_device_is_unlocked_vc(self):
        self.mock_cli.get_volume.return_value = self.mock_vc_volume_mounted

        assert self.service.scan_all_devices() == Status.DEVICE_WRITABLE

    def test_export_already_mounted_no_cleanup(self):
        self.mock_cli.get_volume.return_value = self.mock_luks_volume_mounted
        with mock.patch.object(self.mock_cli, "write_data_to_device") as mock_write:
            result = self.service.export()

        assert result == Status.SUCCESS_EXPORT
        mock_write.assert_called_once_with(
            self.mock_luks_volume_mounted,
            self.mock_submission.tmpdir,
            self.mock_submission.target_dirname,
        )

    def test_export_write_error(self):
        self.mock_cli.get_volume.return_value = self.mock_luks_volume_mounted
        self.mock_cli.write_data_to_device.side_effect = ExportException(
            sdstatus=Status.ERROR_EXPORT
        )

        assert self.service.export() == Status.ERROR_EXPORT

    def test_export_unlock_error(self):
        self.mock_cli.get_volume.return_value = self.mock_luks_volume_unmounted
        self.mock_cli.unlock_volume.side_effect = ExportException(
            sdstatus=Status.ERROR_UNLOCK_LUKS
        )

        assert self.service.export() == Status.ERROR_UNLOCK_LUKS

    def test_export_unlock_error_unspecified(self):
        self.mock_cli.get_volume.return_value = self.mock_luks_volume_unmounted
        with mock.patch.object(self.mock_cli, "unlock_volume") as mock_unlock:
            mock_unlock.side_effect = ExportException("oh no!")
            result = self.service.export()

        assert result == Status.ERROR_EXPORT
