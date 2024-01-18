"""
Sample output from `lsblk` used as input in `test_cli.py`
"""

### Cli.get_volume(): Supported ###

LSBLK_VALID_DEVICE_LOCKED = b'{ "blockdevices": \n{"name":"sda", "type":"disk", "rm":true, "ro":False, "mountpoint":null, "fstype":null, "children": [ \n{"name":"sda1", "type":"part", "rm":true, "ro":False, "mountpoint":null, "fstype":null}, {"name":"sda2", "type":"part", "rm":true, "ro":False, "mountpoint":null, "fstype":"crypto_LUKS"} ] } ] }'

LSBLK_VALID_DEVICE_WRITABLE = b'{"blockdevices": [{"name":"sda", "type":"disk", "rm":true, "ro":False, "mountpoint":null, "fstype":null,"children": [{"name":"sda1", "type":"part", "rm":true, "ro":False, "mountpoint":null, "fstype":"crypto_LUKS","children": [{"name":"luks-dbfb85f2-77c4-4b1f-99a9-2dd3c6789094", "type":"crypt", "rm":False, "mountpoint":"/media/usb", "fstype":"ext4"}]}]},{"name":"xvda", "type":"disk", "rm":False, "ro":False, "mountpoint":null, "fstype":null,"children": [{"name":"xvda1", "type":"part", "rm":False, "ro":False, "mountpoint":null, "fstype":null},{"name":"xvda2", "type":"part", "rm":False, "ro":False, "mountpoint":null, "fstype":null},{"name":"xvda3", "type":"part", "rm":False, "ro":False, "mountpoint":"/", "fstype":"ext4"}]}]}'

LSBLK_VALID_DEVICE_WRITABLE_VC = b'{"blockdevices": [ {"name":"sda", "rm":true, "ro":False, "type":"disk", "mountpoint":null, "fstype":null, "children": [ {"name":"sda1", "rm":true, "ro":False, "type":"part", "mountpoint":null, "fstype":null, "children": [ {"name":"tcrypt-2049", "rm":False, "ro":False, "type":"crypt", "mountpoint":null, "fstype":"vfat"}]}, {"name":"sda2", "rm":true, "ro":False, "type":"part", "mountpoint":null, "fstype":"ext4"}]}]}'

LSBLK_VALID_MULTIPART_DEVICE_LOCKED_PLUS_INVALID_DEVICE_INSERTED = b'{"blockdevices": [{"name":"sda", "type":"disk", "rm":true, "ro":False, "mountpoint":null, "fstype":null, "children": [{"name":"sda1", "type":"part", "rm":true, "ro":False, "mountpoint":null, "fstype":null}, {"name":"sda2", "type":"part", "rm":true, "ro":False, "mountpoint":null, "fstype":"crypto_LUKS"}]}, {"name":"sdb", "type":"disk", "rm":true, "mountpoint":null, "fstype":null, "children": [ {"name":"sdb1", "type":"part", "rm":False, "mountpoint":"/media/unencrypted", "fstype":"ext4"},]}]}'

LSBLK_VALID_MULTIPART_DEVICE_WRITABLE = b'{"blockdevices": [{"name":"sda", "type":"disk", "rm":true, "ro":false, "mountpoint":null, "fstype":null,"children": [{"name":"sda1", "type":"part", "rm":true, "ro":false, "mountpoint":null, "fstype":null}, {"name":"sda2", "type":"part", "rm":true, "ro":false, "mountpoint":null, "fstype":"crypto_LUKS","children": [ {"name":"luks-dbfb85f2-77c4-4b1f-99a9-2dd3c6789094", "type":"crypt", "rm":false, "mountpoint":"/media/usb", "fstype":"ext4"}]}]},{"name":"xvda", "type":"disk", "rm":false, "ro":false, "mountpoint":null, "fstype":null,"children": [{"name":"xvda1", "type":"part", "rm":false, "ro":false, "mountpoint":null, "fstype":null},{"name":"xvda2", "type":"part", "rm":false, "ro":false, "mountpoint":null, "fstype":null},{"name":"xvda3", "type":"part", "rm":false, "ro":false, "mountpoint":"/", "fstype":"ext4"}]}]}'

### Cli.get_volume(): Unsupported ###

LSBLK_ERROR_MULTI_DEVICE_INSERTED = b'{"blockdevices": [{"name":"sda", "type":"disk", "rm":true, "ro":false, "mountpoint":null, "fstype":null,"children": [{"name":"sda1", "type":"part", "rm":true, "ro":false, "mountpoint":null, "fstype":null},{"name":"sda2", "type":"part", "rm":true, "ro":false, "mountpoint":null, "fstype":"crypto_LUKS"}]},{"name":"sdb", "type":"disk", "rm":true, "ro":false, "mountpoint":null, "fstype":null,"children": [{"name":"sda1", "type":"part", "rm":true, "ro":false, "mountpoint":null, "fstype":null},{"name":"sda2", "type":"part", "rm":true, "ro":false, "mountpoint":null, "fstype":"crypto_LUKS"}]}]}'

LSBLK_ERROR_NO_DEVICE = b'{"blockdevices": [{"name":"sda", "type":"disk", "rm":true, "ro":true, "mountpoint":null, "fstype":null,"children": [{"name":"sda1", "type":"part", "rm":true, "ro":true, "mountpoint":null, "fstype":null},{"name":"sda2", "type":"part", "rm":true, "ro":true, "mountpoint":null, "fstype":"crypto_LUKS"}]}]}'

LSBLK_ERROR_DEVICE_MULTI_ENC_PARTITION = b'{"blockdevices": [{"name":"sda", "type":"disk", "rm":true, "ro":false, "mountpoint":null, "fstype":null,"children": [{"name":"sda1", "type":"part", "rm":true, "ro":true, "mountpoint":null, "fstype":null},{"name":"sda2", "type":"part", "rm":true, "ro":true, "mountpoint":null, "fstype":"crypto_LUKS"},{"name":"sda3", "type":"part", "rm":true, "ro":true, "mountpoint":null, "fstype":"crypto_LUKS"}]}]}'

LSBLK_ERROR_PARTITIONS_TOO_NESTED = b'{"blockdevices": [{"name":"sda", "type":"disk", "rm":true, "ro":false, "mountpoint":null, "fstype":null,"children": [{"name":"sda1", "type":"part", "rm":true, "ro":false, "mountpoint":null, "fstype":null},{"name":"sda2", "type":"part", "rm":true, "ro":false, "mountpoint":null, "fstype":null,"children": [{"name":"sda2p1", "type":"part", "rm":true, "ro":false, "mountpoint":null, "fstype":"crypto_LUKS"}]}]},{"name":"sdb", "type":"disk", "rm":true, "ro":false, "mountpoint":null, "fstype":null,"children": [{"name":"sda1", "type":"part", "rm":true, "ro":false, "mountpoint":null, "fstype":null},{"name":"sda2", "type":"part", "rm":true, "ro":false, "mountpoint":null, "fstype":"crypto_LUKS"}]}]}'

LSBLK_ERROR_PARTITION_MOUNTED_NOT_ENCRYPTED = b'{"blockdevices": [{"name":"sda", "type":"disk", "rm":true, "ro":false, "mountpoint":"/media/unencrypted", "fstype":"ext4"},]}'

# Cli._parse_single_volume(): Supported

SINGLE_DEVICE_LOCKED = {
    "name": "sda",
    "type": "disk",
    "rm": True,
    "ro": False,
    "mountpoint": None,
    "fstype": "crypto_LUKS",
}


SINGLE_DEVICE_MULTIPART_LOCKED = {
    "name": "sda",
    "type": "disk",
    "rm": True,
    "ro": False,
    "mountpoint": None,
    "fstype": None,
    "children": [
        {
            "name": "sda1",
            "type": "part",
            "rm": True,
            "ro": False,
            "mountpoint": None,
            "fstype": None,
        },
        {
            "name": "sda2",
            "type": "part",
            "rm": True,
            "ro": False,
            "mountpoint": None,
            "fstype": "crypto_LUKS",
        },
    ],
}

SINGLE_DEVICE_WRITABLE = {
    "name": "sda",
    "type": "disk",
    "rm": True,
    "ro": False,
    "mountpoint": None,
    "fstype": None,
    "children": [
        {
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
    ],
}

SINGLE_DEVICE_UNLOCKED_VC_UNMOUNTED = {
    "name": "sda",
    "rm": True,
    "ro": False,
    "type": "disk",
    "mountpoint": None,
    "fstype": None,
    "children": [
        {
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
        },
        {
            "name": "sda2",
            "rm": True,
            "ro": False,
            "type": "part",
            "mountpoint": None,
            "fstype": "ext4",
        },
    ],
}

SINGLE_DEVICE_WRITABLE_SECOND_PART = {
    "name": "sda",
    "type": "disk",
    "rm": True,
    "ro": False,
    "mountpoint": None,
    "fstype": None,
    "children": [
        {
            "name": "sda1",
            "type": "part",
            "rm": True,
            "ro": False,
            "mountpoint": None,
            "fstype": None,
        },
        {
            "name": "sda2",
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
        },
    ],
}

### Cli._parse_single_volume(): Unsupported ###

SINGLE_DEVICE_ERROR_MULTI_ENC_PARTITION = {
    "name": "sda",
    "type": "disk",
    "rm": True,
    "ro": False,
    "mountpoint": None,
    "fstype": None,
    "children": [
        {
            "name": "sda1",
            "type": "part",
            "rm": True,
            "ro": True,
            "mountpoint": None,
            "fstype": None,
        },
        {
            "name": "sda2",
            "type": "part",
            "rm": True,
            "ro": True,
            "mountpoint": None,
            "fstype": "crypto_LUKS",
        },
        {
            "name": "sda3",
            "type": "part",
            "rm": True,
            "ro": True,
            "mountpoint": None,
            "fstype": "crypto_LUKS",
        },
    ],
}

SINGLE_DEVICE_ERROR_PARTITIONS_TOO_NESTED = {
    "name": "sda",
    "type": "disk",
    "rm": True,
    "ro": False,
    "mountpoint": None,
    "fstype": None,
    "children": [
        {
            "name": "sda1",
            "type": "part",
            "rm": True,
            "ro": False,
            "mountpoint": None,
            "fstype": None,
        },
        {
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
        },
    ],
}

SINGLE_DEVICE_ERROR_MOUNTED_PARTITION_NOT_ENCRYPTED = {
    "name": "sda",
    "type": "disk",
    "rm": True,
    "ro": False,
    "mountpoint": None,
    "fstype": None,
    "children": [
        {
            "name": "sda1",
            "type": "part",
            "rm": True,
            "ro": False,
            "mountpoint": None,
            "fstype": None,
        },
        {
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
        },
    ],
}
