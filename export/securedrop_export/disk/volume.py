from enum import Enum
import os


class EncryptionScheme(Enum):
    """
    Supported encryption schemes.
    """

    UNKNOWN = 0
    LUKS = 1
    VERACRYPT = 2


class Volume:
    MAPPED_VOLUME_PREFIX = "/dev/mapper/"

    """
    A volume on a removable device.
    Volumes have a device name ("/dev/sdX"), and may have a mapped name
    ("/dev/mapper/xxx"), an encryption scheme, and a mountpoint.
    """

    def __init__(
        self,
        device_name: str,
        mapped_name: str,
        encryption: EncryptionScheme,
    ):
        self.device_name = device_name
        self.mapped_name = mapped_name
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

    @property
    def unlocked(self) -> bool:
        return (
            self.mapped_name is not None
            and self.encryption is not None
            and self.encryption is not EncryptionScheme.UNKNOWN
            and os.path.exists(
                os.path.join(self.MAPPED_VOLUME_PREFIX, self.mapped_name)
            )
        )


class MountedVolume(Volume):
    """
    An unlocked and mounted Volume.
    """

    def __init__(
        self,
        device_name: str,
        mapped_name: str,
        encryption: EncryptionScheme,
        mountpoint: str,
    ):
        super().__init__(
            device_name=device_name, mapped_name=mapped_name, encryption=encryption
        )
        self.mountpoint = mountpoint

    @classmethod
    def from_volume(cls, vol: Volume, mountpoint: str):
        return cls(
            device_name=vol.device_name,
            mapped_name=vol.mapped_name,
            encryption=vol.encryption,
            mountpoint=mountpoint,
        )
