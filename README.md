[![CircleCI](https://circleci.com/gh/freedomofpress/securedrop-export.svg?style=svg)](https://circleci.com/gh/freedomofpress/securedrop-export)

# securedrop-export

Code for exporting and printing files from the SecureDrop Qubes Workstation.


## Export Archive Format

Export archive format is defined as a gzipped tar archive whose extension ends with .sd-export.

### Archive Contents

Once extracted, the archive will contain two elements:

`metadata.json` : file containing export metadata, a file containing information about the archive and the export operation

`export_data`: folder containing the raw files to export

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
`device` specifies the method used for export, and can be either a device or a preflight check. See the Devices section below for possible values. It is a required key.

`encryption_method`:
`encryption_method` is used exclusively when exporting to USB storage. It is an optional key. Possible values are:
luks

`encryption_passphrase`
`encryption_passphrase` is used exclusively when exporting to USB storage. It is an optional key. It contains an arbitrary string that contains the disk encryption passphrase of the device.


Example archive metadata (`metadata.json`):
```
{
  "device": "disk"
  "encryption-method": "luks"
  "encryption-key": "Your encryption passphrase goes here"
}
```

### Devices

For all 5 devices described below, there are three generic errors that apply:

`ERROR_FILE_NOT_FOUND`: No file has been specified or the path is incorrect
`ERROR_EXTRACTION`: Error while extracting the archive
`ERROR_METADATA_PARSING`: The metadata.json file cannot be correctly parsed
`ERROR_ARCHIVE_METADATA`: The metadata failed the check
`ERROR_GENERIC`: An uncaught (unexpected) error somewhere in the script. These should not happen unless the code improperly handles errors

The list of devices are as follows:

1. `usb-test` : Preflight check that probes for USB connected devices, that returns:
`USB_CONNECTED` if a USB device is attached to the dedicated slot
`USB_NOT_CONNECTED` if no USB is attached
`USB_CHECK_ERROR` if an error occurred during pre-flight

2. `disk-test`: Preflight check that checks for LUKS-encrypted volume that returns:
`USB_ENCRYPTED` if a LUKS volume is attached to sd-export
`USB_ENCRYPTION_NOT_SUPPORTED` if a LUKS volume is not attached or there was any other error
`USB_DISK_ERROR`

3. `printer-test`: prints a test page that returns:
`ERROR_PRINTER_NOT_FOUND` if no printer is connected
`ERROR_PRINTER_NOT_SUPPORTED` if the printer is not currently supported by the export script
`ERROR_PRINTER_DRIVER_UNAVAILABLE` if the printer driver is not available
`ERROR_PRINTER_INSTALL` If there is an error installing the printer
`ERROR_PRINT` if there is an error printing

4. `printer`: sends files to printer that returns:
`ERROR_PRINTER_NOT_FOUND` if no printer is connected
`ERROR_PRINTER_NOT_SUPPORTED` if the printer is not currently supported by the export script
`ERROR_PRINTER_DRIVER_UNAVAILABLE` if the printer driver is not available
`ERROR_PRINTER_INSTALL` If there is an error installing the printer
`ERROR_PRINT` if there is an error printing

5. `disk`: sends files to disk:
All files in `export_data` will be sent to disk
`encryption_method` and `encryption_passphrase` specify the device encryption settings

### Export Folder Structure

When exporting to a USB drive (using the disk device in metadata.json), the files will be placed on the drive as follows: The root of the USB drive will contain one folder per source, reflecting their source codename in the client. Documents or messages exported will be copied to that directory, preserving the filename from the server. In case a same file is exported twice, a confirmation window replace/rename/abort.

Example folder structure of USB export drive:

```
.

├── cytotoxic payer
│   ├── 1-cytotoxic-payer-msg
│   │   └── file-to-export-1.txt
│   ├── 2-cytotoxic-payer-msg
│   │   └── file-to-export-2.txt
│   └── 3-cytotoxic-payer-doc
│   │   └── file-to-export-3.doc
├── grandiloquent pasteboard
│   └── 1-grandiloquent-pasteboard-doc
│   │   └── file-to-export-1.doc
└── snug seek
```

