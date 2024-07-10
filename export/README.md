# securedrop-export

Code for exporting and printing files from the SecureDrop Qubes Workstation.

## Quick Start

1. [Install Poetry](https://python-poetry.org/docs/#installing-with-the-official-installer)
2. Run `make check` to verify the installation

## Supported Printers

Printer support is currently limited to a subset of Brother and HP printers that offer USB
(non-wireless) connectivity, such as:

- HP LaserJet Pro 4001dn
- Brother HL-L2320D

## Supported Export Devices

Export to LUKS-encrypted or VeraCrypt-encrypted USB devices is supported.

### LUKS
Partition a drive (either the MBR/DOS or the GPT partition scheme is fine)
and encrypt exactly one partition with LUKS.  On Linux, you can
[follow these instructions](https://docs.securedrop.org/en/stable/set_up_transfer_and_export_device.html#create-usb-transfer-device)
to use GNOME Disks to set up your drive.  You can also use
[cryptsetup](https://linux.die.net/man/8/cryptsetup):

1. `sudo cryptsetup luksFormat --hash=sha512 --key-size=512 DEVICE` where `DEVICE`
   is the name of your removable drive, which you can find via `lsblk -p`.

   Make sure `DEVICE` is correct because you will be overwriting its data irrevocably.

2. `sudo cryptsetup luksOpen /dev/sdb encrypted_device`

3. `sudo mkfs.ext4 /dev/mapper/encrypted_device`

4. `sudo cryptsetup luksClose /dev/mapper/encrypted_device`

### VeraCrypt
[Download and verify](https://www.veracrypt.fr/) VeraCrypt or VeraCrypt CLI and follow the
documentation to provision a USB drive. When provisioning VeraCrypt drives, ensure that the
filesystem is Linux-compatible. (FAT32 is suggested for cross-platform compatibility).

VeraCrypt devices must be manually unlocked in order to be detected for export. Users
will be prompted during the export workflow.

Unlock a VeraCrypt device using the commandline in `sd-devices` by typing
`udisksctl unlock -b /dev/sdXX`, where `/dev/sdXX` is the device as identified in
the Devices widget (for example, `/dev/sda1`) or as identified by `lsblk -p`.

## Export Archive Format

Export archive format is defined as a gzipped tar archive whose extension ends with `.sd-export`.

### Archive Contents

Once extracted, the archive will contain two elements:

`metadata.json`
: file containing export metadata, a file containing information about the archive and the export operation

`export_data`
: folder containing the raw files to export

Example archive structure:

```
.
├── metadata.json
└── export_data
    ├── file-to-export-1.txt
    ├── file-to-export-2.pdf
    ├── file-to-export-3.doc
    [...]
```

### Archive Metadata

Metadata contains three possible keys which may contain several possible values:

`device`
: specifies the method used for export, and can be either a device or a preflight check. See the Devices section below for possible values. It is a required key.


`encryption_passphrase`
: used exclusively when exporting to USB storage. It is an optional key. It contains an arbitrary string that contains the disk encryption passphrase of the device.


Example archive metadata (`metadata.json`):
```
{
  "device": "disk"
  "encryption-key": "Your encryption passphrase goes here"
}
```

### Devices

For all device types (described in detail below), the following standard error types can be returned:

- `ERROR_FILE_NOT_FOUND`: No file has been specified or the path is incorrect
- `ERROR_EXTRACTION`: Error while extracting the archive
- `ERROR_METADATA_PARSING`: The metadata.json file cannot be correctly parsed
- `ERROR_ARCHIVE_METADATA`: The metadata failed the check
- `ERROR_USB_CONFIGURATION`: There is no USB controller attached to the VM
- `ERROR_GENERIC`: An uncaught (unexpected) error somewhere in the script. These should not happen unless the code improperly handles errors

The supported device types for export are as follows, including the possible errors specific to that device type:

1. `disk-test`: Preflight check that probes for USB connected devices, that returns:
    - `NO_DEVICE_DETECTED`, `MULTI_DEVICE_DETECTED`: wrong number of inserted USB drives
    - `INVALID_DEVICE_DETECTED`: Wrong number of partitions, unsupported encryption scheme, etc.
       Note: locked VeraCrypt drives also return this status, and a hint is shown to the user that they must
       manually unlock such drives before proceeding.
    - `DEVICE_LOCKED` if a supported drive is inserted but locked (a LUKS drive, since locked Veracrypt detection is not supported)
    - `DEVICE_WRITABLE` if a supported USB device is attached and unlocked. (Only used for Preflight check)
    - `DEVICE_ERROR`: A problem was encountered and device state cannot be reported.

2. `disk`: Attempts to send files to disk. Can return any Preflight status except `DEVICE_WRITABLE`, as well as
    the following status results below, which replace `DEVICE_WRITABLE` since they attempt the export action.
    Because export is a linear process, a status such as `ERROR_EXPORT_CLEANUP` indicates that the file export
    succeeded and the problem occurred after that point in the process.
    - `ERROR_UNLOCK_LUKS` if LUKS decryption failed due to bad passphrase
    - `ERROR_UNLOCK_GENERIC` if unlocking failed due to some other reason
    - `ERROR_MOUNT` if there was an error mounting the volume
    - `ERROR_UNMOUT_VOLUME_BUSY` if there was an error unmounting the drive after export
    - `ERROR_EXPORT_CLEANUP` if there was an error removing temporary directories after export
    - `SUCCESS_EXPORT`: Entire routine, including export and cleanup, was successful

3. `printer-preflight`, `printer-test`: test the printer and ensure it is ready.
    - `ERROR_PRINTER_NOT_FOUND` if no printer is connected
    - `ERROR_PRINTER_NOT_SUPPORTED` if the printer is not currently supported by the export script
    - `ERROR_PRINTER_DRIVER_UNAVAILABLE` if the printer driver is not available
    - `ERROR_PRINTER_URI` if `lpinfo` fails to retrieve printer information
    - `ERROR_PRINTER_INSTALL` If there is an error installing the printer
    - `ERROR_PRINT` if there is an error printing
    - `PRINT_PREFLIGHT_SUCCESS` if preflight checks were successful (Preflight only)

4. `printer`: sends files to printer that returns any of the `printer-preflight` statuses except
    `PRINT_PREFLIGHT_SUCCESS`, as well as:
    - `PRINT_SUCCESS` if the job is dispatched successfully

### Export Folder Structure

When exporting to a USB drive, the files will be placed on the drive as follows: The root of the USB drive will contain one `sd-export-[timestamp]` folder, where `[timestamp]` is in the format `YYYYMMDD-hhmmss`. This folder will contain a subfolder `export_data`, which will contain the exported file with its original name as submitted by the source. For example:

```
.

└── sd-export-20200116-003153
    └── export_data
        └── transcript.txt
        └── secret_memo.pdf
```

To support multiple files, in the long term, we are planning to use a folder structure similar to the following, where the journalist designation for a source is used for folder names and message/reply file names.


```
.

├── cytotoxic-payer
│   ├── 1-cytotoxic-payer-msg
│   │   └── 1-cytotoxic-payer-msg.txt
│   ├── 2-cytotoxic-payer-msg
│   │   └── 2-cytotoxic-payer-msg.txt
│   └── 3-cytotoxic-payer-doc
│   │   └── interesting_file.doc
├── grandiloquent-pasteboard
│   └── 1-grandiloquent-pasteboard-doc
│   │   └── questionable_file.pdf
└── snug-seek
```
