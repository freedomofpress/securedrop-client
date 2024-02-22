"""
Sample output from `lsblk` used as input in `test_cli.py`
"""

# udisks2 Status
UDISKS_STATUS_NOTHING_CONNECTED = (
    b"MODEL                     REVISION  SERIAL               DEVICE"
    b"\n--------------------------------------------------------------------------\n"
)

UDISKS_STATUS_ONE_DEVICE_CONNECTED = (
    b"MODEL                     REVISION  SERIAL               DEVICE\n"
    b"--------------------------------------------------------------------------\n"
    b"ADATA USB Flash Drive     1.00      2761505420110004     sda     \n"
)
UDISKS_STATUS_MULTI_CONNECTED = (
    b"MODEL                     REVISION  SERIAL               DEVICE\n"
    b"--------------------------------------------------------------------------\n"
    b"ADATA USB Flash Drive     1.00      2761505420110004     sda     \n"
    b"Kingston DataTraveler 3.0 PMAP      40B0767E212CE481165906A8 sdb     \n"
)

# CLI.get_volume(): Supported
ONE_DEVICE_LUKS_UNMOUNTED = b'{\n   "blockdevices": [\n      {"name":"sda", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"sda1", "ro":false, "type":"part", "mountpoint":null, "fstype":null},\n            {"name":"sda2", "ro":false, "type":"part", "mountpoint":null, "fstype":"crypto_LUKS"}\n         ]\n      },\n      {"name":"xvda", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"xvda1", "ro":false, "type":"part", "mountpoint":null, "fstype":null},\n            {"name":"xvda2", "ro":false, "type":"part", "mountpoint":null, "fstype":null},\n            {"name":"xvda3", "ro":false, "type":"part", "mountpoint":"/", "fstype":"ext4"}\n         ]\n      },\n      {"name":"xvdb", "ro":false, "type":"disk", "mountpoint":"/rw", "fstype":"ext4"},\n      {"name":"xvdc", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"xvdc1", "ro":false, "type":"part", "mountpoint":"[SWAP]", "fstype":"swap"},\n            {"name":"xvdc3", "ro":false, "type":"part", "mountpoint":null, "fstype":null}\n         ]\n      },\n      {"name":"xvdd", "ro":true, "type":"disk", "mountpoint":null, "fstype":"ext3"}\n   ]\n}\n'  # noqa: E501

ONE_DEVICE_VC_UNLOCKED = b'{\n   "blockdevices": [\n      {"name":"sda", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"sda1", "ro":false, "type":"part", "mountpoint":null, "fstype":null,\n               "children": [\n                  {"name":"tcrypt-2049", "ro":false, "type":"crypt", "mountpoint":null, "fstype":"vfat"}\n               ]\n            },\n            {"name":"sda2", "ro":false, "type":"part", "mountpoint":null, "fstype":"ext4"}\n         ]\n      },\n      {"name":"xvda", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"xvda1", "ro":false, "type":"part", "mountpoint":null, "fstype":null},\n            {"name":"xvda2", "ro":false, "type":"part", "mountpoint":null, "fstype":null},\n            {"name":"xvda3", "ro":false, "type":"part", "mountpoint":"/", "fstype":"ext4"}\n         ]\n      },\n      {"name":"xvdb", "ro":false, "type":"disk", "mountpoint":"/rw", "fstype":"ext4"},\n      {"name":"xvdc", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"xvdc1", "ro":false, "type":"part", "mountpoint":"[SWAP]", "fstype":"swap"},\n            {"name":"xvdc3", "ro":false, "type":"part", "mountpoint":null, "fstype":null}\n         ]\n      },\n      {"name":"xvdd", "ro":true, "type":"disk", "mountpoint":null, "fstype":"ext3"}\n   ]\n}\n'  # noqa: E501

ONE_DEVICE_VC_MOUNTED = b'{\n   "blockdevices": [\n      {"name":"sda", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"sda1", "ro":false, "type":"part", "mountpoint":null, "fstype":null,\n               "children": [\n                  {"name":"tcrypt-2049", "ro":false, "type":"crypt", "mountpoint":null, "fstype":"vfat"}\n               ]\n            },\n            {"name":"sda2", "ro":false, "type":"part", "mountpoint":null, "fstype":"ext4"}\n         ]\n      },\n      {"name":"xvda", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"xvda1", "ro":false, "type":"part", "mountpoint":null, "fstype":null},\n            {"name":"xvda2", "ro":false, "type":"part", "mountpoint":null, "fstype":null},\n            {"name":"xvda3", "ro":false, "type":"part", "mountpoint":"/", "fstype":"ext4"}\n         ]\n      },\n      {"name":"xvdb", "ro":false, "type":"disk", "mountpoint":"/rw", "fstype":"ext4"},\n      {"name":"xvdc", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"xvdc1", "ro":false, "type":"part", "mountpoint":"[SWAP]", "fstype":"swap"},\n            {"name":"xvdc3", "ro":false, "type":"part", "mountpoint":null, "fstype":null}\n         ]\n      },\n      {"name":"xvdd", "ro":true, "type":"disk", "mountpoint":null, "fstype":"ext3"}\n   ]\n}\n'  # noqa: E501

ERROR_ONE_DEVICE_LUKS_MOUNTED_MULTI_UNKNOWN_AVAILABLE = b'{\n   "blockdevices": [\n      {"name":"sda", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"sda1", "ro":false, "type":"part", "mountpoint":null, "fstype":null},\n            {"name":"sda2", "ro":false, "type":"part", "mountpoint":null, "fstype":"crypto_LUKS",\n               "children": [\n                  {"name":"luks-dbfb85f2-77c4-4b1f-99a9-2dd3c6789094", "ro":false, "type":"crypt", "mountpoint":"/media/user/tx2", "fstype":"ext4"}\n               ]\n            }\n         ]\n      },\n      {"name":"sdb", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"sdb1", "ro":false, "type":"part", "mountpoint":null, "fstype":null},\n            {"name":"sdb2", "ro":false, "type":"part", "mountpoint":null, "fstype":"ext4"}\n         ]\n      },\n      {"name":"xvda", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"xvda1", "ro":false, "type":"part", "mountpoint":null, "fstype":null},\n            {"name":"xvda2", "ro":false, "type":"part", "mountpoint":null, "fstype":null},\n            {"name":"xvda3", "ro":false, "type":"part", "mountpoint":"/", "fstype":"ext4"}\n         ]\n      },\n      {"name":"xvdb", "ro":false, "type":"disk", "mountpoint":"/rw", "fstype":"ext4"},\n      {"name":"xvdc", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"xvdc1", "ro":false, "type":"part", "mountpoint":"[SWAP]", "fstype":"swap"},\n            {"name":"xvdc3", "ro":false, "type":"part", "mountpoint":null, "fstype":null}\n         ]\n      },\n      {"name":"xvdd", "ro":true, "type":"disk", "mountpoint":null, "fstype":"ext3"}\n   ]\n}\n'  # noqa: E501

ERROR_NO_SUPPORTED_DEVICE = b'{\n   "blockdevices": [\n      {"name":"sdb", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"sdb1", "ro":false, "type":"part", "mountpoint":null, "fstype":null},\n            {"name":"sdb2", "ro":false, "type":"part", "mountpoint":null, "fstype":"ext4"}\n         ]\n      },\n      {"name":"xvda", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"xvda1", "ro":false, "type":"part", "mountpoint":null, "fstype":null},\n            {"name":"xvda2", "ro":false, "type":"part", "mountpoint":null, "fstype":null},\n            {"name":"xvda3", "ro":false, "type":"part", "mountpoint":"/", "fstype":"ext4"}\n         ]\n      },\n      {"name":"xvdb", "ro":false, "type":"disk", "mountpoint":"/rw", "fstype":"ext4"},\n      {"name":"xvdc", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"xvdc1", "ro":false, "type":"part", "mountpoint":"[SWAP]", "fstype":"swap"},\n            {"name":"xvdc3", "ro":false, "type":"part", "mountpoint":null, "fstype":null}\n         ]\n      },\n      {"name":"xvdd", "ro":true, "type":"disk", "mountpoint":null, "fstype":"ext3"}\n   ]\n}\n'  # noqa: E501

ERROR_UNENCRYPTED_DEVICE_MOUNTED = b'{\n   "blockdevices": [\n      {"name":"sda", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"sda1", "ro":false, "type":"part", "mountpoint":null, "fstype":null,\n               "children": [\n                  {"name":"decoy", "ro":false, "type":"part", "mountpoint":"/media/usb", "fstype":"vfat"}\n               ]\n            },\n            {"name":"sda2", "ro":false, "type":"part", "mountpoint":null, "fstype":"ext4"}\n         ]\n      },\n      {"name":"xvda", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"xvda1", "ro":false, "type":"part", "mountpoint":null, "fstype":null},\n            {"name":"xvda2", "ro":false, "type":"part", "mountpoint":null, "fstype":null},\n            {"name":"xvda3", "ro":false, "type":"part", "mountpoint":"/", "fstype":"ext4"}\n         ]\n      },\n      {"name":"xvdb", "ro":false, "type":"disk", "mountpoint":"/rw", "fstype":"ext4"},\n      {"name":"xvdc", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"xvdc1", "ro":false, "type":"part", "mountpoint":"[SWAP]", "fstype":"swap"},\n            {"name":"xvdc3", "ro":false, "type":"part", "mountpoint":null, "fstype":null}\n         ]\n      },\n      {"name":"xvdd", "ro":true, "type":"disk", "mountpoint":null, "fstype":"ext3"}\n   ]\n}\n'  # noqa: E501

# CLI.get_volume(): Unsupported
ERROR_DEVICE_MULTI_ENC_PARTITION = b'{\n   "blockdevices": [\n      {"name":"sda", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"sda1", "ro":false, "type":"part", "mountpoint":null, "fstype":null},\n            {"name":"sda2", "ro":false, "type":"part", "mountpoint":null, "fstype":"crypto_LUKS"},\n            {"name":"sda3", "ro":false, "type":"part", "mountpoint":null, "fstype":"crypto_LUKS"}\n         ]\n      },\n      {"name":"xvda", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"xvda1", "ro":false, "type":"part", "mountpoint":null, "fstype":null},\n            {"name":"xvda2", "ro":false, "type":"part", "mountpoint":null, "fstype":null},\n            {"name":"xvda3", "ro":false, "type":"part", "mountpoint":"/", "fstype":"ext4"}\n         ]\n      },\n      {"name":"xvdb", "ro":false, "type":"disk", "mountpoint":"/rw", "fstype":"ext4"},\n      {"name":"xvdc", "ro":false, "type":"disk", "mountpoint":null, "fstype":null,\n         "children": [\n            {"name":"xvdc1", "ro":false, "type":"part", "mountpoint":"[SWAP]", "fstype":"swap"},\n            {"name":"xvdc3", "ro":false, "type":"part", "mountpoint":null, "fstype":null}\n         ]\n      },\n      {"name":"xvdd", "ro":true, "type":"disk", "mountpoint":null, "fstype":"ext3"}\n   ]\n}\n'  # noqa: E501

# Cli._get_supported_volume(): Supported

SINGLE_DEVICE_LOCKED = {
    "name": "sda",
    "type": "disk",
    "rm": True,
    "ro": False,
    "mountpoint": None,
    "fstype": "crypto_LUKS",
}

SINGLE_PART_LUKS_WRITABLE = {
    "name": "sda1",
    "type": "part",
    "rm": True,
    "ro": False,
    "mountpoint": None,
    "fstype": "crypto_LUKS",
    "children": [
        {
            "name": "luks-dbfb85f2-77c4-4b1f-99a9-2dd3c6789094",
            "type": "crypt",
            "rm": False,
            "mountpoint": "/media/usb",
            "fstype": "ext4",
        }
    ],
}

SINGLE_PART_VC_WRITABLE = {
    "name": "sda1",
    "rm": True,
    "ro": False,
    "type": "part",
    "mountpoint": None,
    "fstype": None,
    "children": [
        {
            "name": "tcrypt-2049",
            "rm": False,
            "ro": False,
            "type": "crypt",
            "mountpoint": "/media/usb",
            "fstype": "vfat",
        }
    ],
}

SINGLE_PART_LUKS_UNLOCKED_UNMOUNTED = {
    "name": "sda1",
    "type": "part",
    "rm": True,
    "ro": False,
    "mountpoint": None,
    "fstype": "crypto_LUKS",
    "children": [
        {
            "name": "luks-dbfb85f2-77c4-4b1f-99a9-2dd3c6789094",
            "type": "crypt",
            "rm": False,
            "mountpoint": None,
            "fstype": "ext4",
        }
    ],
}


SINGLE_PART_UNLOCKED_VC_UNMOUNTED = {
    "name": "sda1",
    "rm": True,
    "ro": False,
    "type": "part",
    "mountpoint": None,
    "fstype": None,
    "children": [
        {
            "name": "tcrypt-2049",
            "rm": False,
            "ro": False,
            "type": "crypt",
            "mountpoint": None,
            "fstype": "vfat",
        }
    ],
}

# Cli._get_supported_volume(): Unsupported

SINGLE_DEVICE_ERROR_PARTITIONS_TOO_NESTED = {
    "name": "sda2",
    "type": "part",
    "rm": True,
    "ro": False,
    "mountpoint": None,
    "fstype": None,
    "children": [
        {
            "name": "sda2p1",
            "type": "part",
            "rm": True,
            "ro": False,
            "mountpoint": None,
            "fstype": "crypto_LUKS",
        }
    ],
}

SINGLE_DEVICE_ERROR_MOUNTED_PARTITION_NOT_ENCRYPTED = {
    "name": "sda2",
    "type": "part",
    "rm": True,
    "ro": False,
    "mountpoint": None,
    "fstype": None,
    "children": [
        {
            "name": "unencrypted",
            "type": "part",
            "rm": False,
            "mountpoint": "/media/unencrypted",
            "fstype": "ext4",
        }
    ],
}
