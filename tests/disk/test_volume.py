from unittest import mock

from securedrop_export.disk.volume import Volume, MountedVolume, EncryptionScheme


class TestVolume:
    def test_overwrite_valid_encryption_scheme(self):
        volume = Volume(
            device_name="/dev/sda",
            mapped_name="pretend-luks-mapper-id",
            encryption=EncryptionScheme.LUKS,
        )
        assert volume.encryption is EncryptionScheme.LUKS
        volume.encryption = None
        assert volume.encryption is EncryptionScheme.UNKNOWN

    @mock.patch("os.path.exists", return_value=True)
    def test_is_unlocked_true(self, mock_os_path):
        volume = Volume(
            device_name="/dev/sda1",
            mapped_name="pretend-luks-mapper-id",
            encryption=EncryptionScheme.LUKS,
        )

        assert volume.unlocked

    @mock.patch("os.path.exists", return_value=False)
    def test_is_unlocked_false_no_path(self, mock_os_path):
        volume = Volume(
            device_name="/dev/sda1",
            mapped_name="pretend-luks-mapper-id",
            encryption=EncryptionScheme.LUKS,
        )

        assert not volume.unlocked


class TestMountedVolume:
    @mock.patch("os.path.exists", return_value=True)
    def test_is_unlocked_true(self, mock_os_path):
        volume = Volume(
            device_name="/dev/sda1",
            mapped_name="pretend-luks-mapper-id",
            encryption=EncryptionScheme.LUKS,
        )

        mounted_volume = MountedVolume.from_volume(volume, mountpoint="/media/usb")

        assert mounted_volume.unlocked
        assert mounted_volume.mountpoint == "/media/usb"
