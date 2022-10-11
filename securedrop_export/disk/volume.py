from enum import Enum
import os


class EncryptionScheme(Enum):
    """
    Supported encryption schemes.
    """

    UNKNOWN = 0
    LUKS = 1


class Volume:

    MAPPED_VOLUME_PREFIX = "/dev/mapper/"

    """
    A volume on a removable device.
    Volumes have a device name ("/dev/sdX"), a mapped name ("/dev/mapper/xxx"), an encryption
    scheme, and a mountpoint if they are mounted.
    """

    def __init__(
        self,
        device_name: str,
        mapped_name: str,
        encryption: EncryptionScheme,
        mountpoint: str = None,
    ):
        self.device_name = device_name
        self.mapped_name = mapped_name
        self.mountpoint = mountpoint
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
    def writable(self) -> bool:
        return self.unlocked and self.mountpoint is not None

    @property
    def unlocked(self) -> bool:
        return (
            self.mapped_name is not None
            and self.encryption is not EncryptionScheme.UNKNOWN
            and os.path.exists(
                os.path.join(self.MAPPED_VOLUME_PREFIX, self.mapped_name)
            )
        )
