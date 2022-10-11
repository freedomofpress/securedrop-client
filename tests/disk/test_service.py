import pytest
from unittest import mock
import os
import tempfile

from securedrop_export.exceptions import ExportException
from securedrop_export.disk.status import Status
from securedrop_export.disk.new_status import Status as NewStatus
from securedrop_export.disk.volume import Volume, EncryptionScheme
from securedrop_export.archive import Archive, Metadata
from securedrop_export.disk.service import Service
from securedrop_export.disk.cli import CLI

SAMPLE_OUTPUT_LSBLK_NO_PART = b"disk\ncrypt"  # noqa
SAMPLE_OUTPUT_USB = "/dev/sda"  # noqa
SAMPLE_OUTPUT_USB_PARTITIONED = "/dev/sda1"


class TestExportService:
    @classmethod
    def setup_class(cls):
        cls.mock_cli = mock.MagicMock(CLI)
        cls.mock_submission = cls._setup_submission()

        cls.mock_luks_volume_unmounted = Volume(
            device_name=SAMPLE_OUTPUT_USB,
            mapped_name="fake-luks-id-123456",
            encryption=EncryptionScheme.LUKS,
        )
        cls.mock_luks_volume_mounted = Volume(
            device_name=SAMPLE_OUTPUT_USB,
            mapped_name="fake-luks-id-123456",
            mountpoint="/media/usb",
            encryption=EncryptionScheme.LUKS,
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
        self.mock_cli.get_connected_devices.return_value = [SAMPLE_OUTPUT_USB]
        self.mock_cli.get_partitioned_device.return_value = (
            SAMPLE_OUTPUT_USB_PARTITIONED
        )
        self.mock_cli.get_luks_volume.return_value = self.mock_luks_volume_unmounted
        self.mock_cli.mount_volume.return_value = self.mock_luks_volume_mounted

    def teardown_method(self, method):
        self.mock_cli.reset_mock(return_value=True, side_effect=True)

    def test_check_usb(self):
        status = self.service.check_connected_devices()

        assert status is Status.LEGACY_USB_CONNECTED

    def test_no_devices_connected(self):
        self.mock_cli.get_connected_devices.return_value = []
        with pytest.raises(ExportException) as ex:
            self.service.check_connected_devices()

        assert ex.value.sdstatus is Status.LEGACY_USB_NOT_CONNECTED

    def test_too_many_devices_connected(self):
        self.mock_cli.get_connected_devices.return_value = [
            SAMPLE_OUTPUT_USB,
            "/dev/sdb",
        ]
        with pytest.raises(ExportException) as ex:
            self.service.check_connected_devices()

        assert ex.value.sdstatus is Status.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED

    def test_device_is_not_luks(self):
        self.mock_cli.is_luks_volume.return_value = False

        # When VeraCrypt is supported, this will no longer be an exception
        # and the return status will change
        with pytest.raises(ExportException) as ex:
            self.service.check_disk_format()

        assert ex.value.sdstatus is Status.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED

    def test_check_usb_error(self):
        self.mock_cli.get_connected_devices.side_effect = ExportException(
            sdstatus=Status.LEGACY_ERROR_USB_CHECK
        )

        with pytest.raises(ExportException) as ex:
            self.service.check_connected_devices()

        assert ex.value.sdstatus is Status.LEGACY_ERROR_USB_CHECK

    def test_check_disk_format(self):
        status = self.service.check_disk_format()

        assert status is Status.LEGACY_USB_ENCRYPTED

    def test_check_disk_format_error(self):
        self.mock_cli.get_partitioned_device.side_effect = ExportException(
            sdstatus=NewStatus.INVALID_DEVICE_DETECTED
        )

        with pytest.raises(ExportException) as ex:
            self.service.check_disk_format()

        # We still return the legacy status for now
        assert ex.value.sdstatus is Status.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED

    def test_export(self):
        # Currently, a successful export does not return a success status.
        # When the client is updated, this will change to assert EXPORT_SUCCESS
        # is returned.
        self.service.export()

    def test_export_disk_not_supported(self):
        self.mock_cli.is_luks_volume.return_value = False

        with pytest.raises(ExportException) as ex:
            self.service.export()

        assert ex.value.sdstatus is Status.LEGACY_USB_ENCRYPTION_NOT_SUPPORTED

    def test_export_write_error(self):
        self.mock_cli.is_luks_volume.return_value = True
        self.mock_cli.write_data_to_device.side_effect = ExportException(
            sdstatus=Status.LEGACY_ERROR_USB_WRITE
        )

        with pytest.raises(ExportException) as ex:
            self.service.export()

        assert ex.value.sdstatus is Status.LEGACY_ERROR_USB_WRITE

    def test_export_throws_new_exception_return_legacy_status(self):
        self.mock_cli.get_connected_devices.side_effect = ExportException(
            sdstatus=NewStatus.ERROR_MOUNT
        )

        with pytest.raises(ExportException) as ex:
            self.service.export()

        assert ex.value.sdstatus is Status.LEGACY_ERROR_USB_MOUNT

    @mock.patch("os.path.exists", return_value=True)
    def test_write_error_returns_legacy_status(self, mock_path):
        self.mock_cli.is_luks_volume.return_value = True
        self.mock_cli.write_data_to_device.side_effect = ExportException(
            sdstatus=NewStatus.ERROR_EXPORT
        )

        with pytest.raises(ExportException) as ex:
            self.service.export()

        assert ex.value.sdstatus is Status.LEGACY_ERROR_USB_WRITE

    @mock.patch("os.path.exists", return_value=True)
    def test_unlock_error_returns_legacy_status(self, mock_path):
        self.mock_cli.unlock_luks_volume.side_effect = ExportException(
            sdstatus=NewStatus.ERROR_UNLOCK_LUKS
        )

        with pytest.raises(ExportException) as ex:
            self.service.export()

        assert ex.value.sdstatus is Status.LEGACY_USB_BAD_PASSPHRASE

    @mock.patch("os.path.exists", return_value=True)
    def test_unexpected_error_returns_legacy_status_generic(self, mock_path):
        self.mock_cli.unlock_luks_volume.side_effect = ExportException(
            sdstatus=NewStatus.DEVICE_ERROR
        )

        with pytest.raises(ExportException) as ex:
            self.service.export()

        assert ex.value.sdstatus is Status.LEGACY_ERROR_GENERIC
