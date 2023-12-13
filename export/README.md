# securedrop-export

Code for exporting and printing files from the SecureDrop Qubes Workstation.

## Quick Start

1. [Install Poetry](https://python-poetry.org/docs/#installing-with-the-official-installer)
2. Run `make check` to verify the installation

## Supported Printers

TBD

## Supported Export Devices

We support luks-encrypted drives that are either MBR/DOS partitioned or GPT partitioned. If you use `Disks` in Linux to partition your drive, you can [follow these instructions](https://docs.securedrop.org/en/stable/set_up_transfer_and_export_device.html#create-usb-transfer-device) to create a new export device. You can also use [cryptsetup](https://linux.die.net/man/8/cryptsetup) to create a luks-encrypted device with full-disk encryption, for example:

1. `sudo cryptsetup luksFormat --hash=sha512 --key-size=512 DEVICE` where `DEVICE` is the name of your removable drive, which you can find via `lsblk -p`.

   Make sure `DEVICE` is correct because you will be overwriting its data irrevocably.

2. `sudo cryptsetup luksOpen /dev/sdb encrypted_device`

3. `sudo mkfs.ext4 /dev/mapper/encrypted_device`

4. `sudo cryptsetup luksClose /dev/mapper/encrypted_device`

We do not yet support drives that use full-disk encryption with VeraCrypt.

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

`encryption_method`
: used exclusively when exporting to USB storage. It is an optional key. Possible values are:
luks

`encryption_passphrase`
: used exclusively when exporting to USB storage. It is an optional key. It contains an arbitrary string that contains the disk encryption passphrase of the device.


Example archive metadata (`metadata.json`):
```
{
  "device": "disk"
  "encryption-method": "luks"
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

1. `usb-test` : Preflight check that probes for USB connected devices, that returns:
    - `USB_CONNECTED` if a USB device is attached to the dedicated slot
    - `USB_NOT_CONNECTED` if no USB is attached
    - `USB_CHECK_ERROR` if an error occurred during pre-flight

2. `disk-test`: Preflight check that checks for LUKS-encrypted volume that returns:
    - `USB_ENCRYPTED` if a LUKS volume is attached to sd-devices
    - `USB_ENCRYPTION_NOT_SUPPORTED` if a LUKS volume is not attached or there was any other error
    - `USB_DISK_ERROR`

3. `printer-test`: prints a test page that returns:
    - `ERROR_PRINTER_NOT_FOUND` if no printer is connected
    - `ERROR_PRINTER_NOT_SUPPORTED` if the printer is not currently supported by the export script
    - `ERROR_PRINTER_DRIVER_UNAVAILABLE` if the printer driver is not available
    - `ERROR_PRINTER_INSTALL` If there is an error installing the printer
    - `ERROR_PRINT` if there is an error printing

4. `printer`: sends files to printer that returns:
    - `ERROR_PRINTER_NOT_FOUND` if no printer is connected
    - `ERROR_PRINTER_NOT_SUPPORTED` if the printer is not currently supported by the export script
    - `ERROR_PRINTER_DRIVER_UNAVAILABLE` if the printer driver is not available
    - `ERROR_PRINTER_INSTALL` If there is an error installing the printer
    - `ERROR_PRINT` if there is an error printing

5. `disk`: sends files to disk that returns:
    - `USB_BAD_PASSPHRASE` if the luks decryption failed (likely due to bad passphrase)
    - `ERROR_USB_MOUNT` if there was an error mounting the volume (after unlocking the luks volume)
    - `ERROR_USB_WRITE` if there was an error writing to disk (e.g., no space left on device)

### Export Folder Structure

When exporting to a USB drive, the files will be placed on the drive as follows: The root of the USB drive will contain one `sd-export-[timestamp]` folder, where `[timestamp]` is in the format `YYYYMMDD-hhmmss`. This folder will contain a subfolder `export_data`, which will contain the exported file with its original name as submitted by the source. For example:

```
.

└── sd-export-20200116-003153
    └── export_data
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
