from enum import Enum


class EncryptionScheme(Enum):
    """
    Supported encryption schemes.
    """

    UNKNOWN = 0
    LUKS = 1
    VERACRYPT = 2


class Volume:
    """
    A volume on a removable device.
    Volumes have a device name ("/dev/sdX") and an encryption scheme.
    """

    def __init__(
        self,
        device_name: str,
        encryption: EncryptionScheme,
    ):
        self.device_name = device_name
        self.encryption = encryption

    @property
    def encryption(self):
        return self._encryption

    @encryption.setter
    def encryption(self, scheme: EncryptionScheme):
        if scheme:
            self._encryption = scheme
        else:
            self._encryption = EncryptionScheme.UNKNOWN


class MountedVolume(Volume):
    """
    An unlocked and mounted Volume.

    Device name (from Volume) and unlocked name
    are full paths (/dev/sdX, /dev/dm-X, /dev/mapper/idx).
    """

    def __init__(
        self,
        device_name: str,
        unlocked_name: str,
        encryption: EncryptionScheme,
        mountpoint: str,
    ):
        super().__init__(device_name=device_name, encryption=encryption)
        self.unlocked_name = unlocked_name
        self.mountpoint = mountpoint
