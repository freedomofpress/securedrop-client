#!/usr/bin/env python3

import datetime
import json
import logging
import os
import shutil
import signal
import subprocess
import sys
import tarfile
import tempfile
import time

from enum import Enum

PRINTER_NAME = "sdw-printer"
PRINTER_WAIT_TIMEOUT = 60
DEVICE = "/dev/sda"
MOUNTPOINT = "/media/usb"
ENCRYPTED_DEVICE = "encrypted_volume"
BRLASER_DRIVER = "/usr/share/cups/drv/brlaser.drv"
BRLASER_PPD = "/usr/share/cups/model/br7030.ppd"

logger = logging.getLogger(__name__)


class ExportStatus(Enum):

    # General errors
    ERROR_FILE_NOT_FOUND = 'ERROR_FILE_NOT_FOUND'
    ERROR_EXTRACTION = 'ERROR_EXTRACTION'
    ERROR_METADATA_PARSING = 'ERROR_METADATA_PARSING'
    ERROR_ARCHIVE_METADATA = 'ERROR_ARCHIVE_METADATA'
    ERROR_USB_CONFIGURATION = 'ERROR_USB_CONFIGURATION'
    ERROR_GENERIC = 'ERROR_GENERIC'

    # USB preflight related errors
    USB_CONNECTED = 'USB_CONNECTED'
    USB_NOT_CONNECTED = 'USB_NOT_CONNECTED'
    ERROR_USB_CHECK = 'ERROR_USB_CHECK'

    # USB Disk preflight related errors
    USB_ENCRYPTED = 'USB_ENCRYPTED'
    USB_ENCRYPTION_NOT_SUPPORTED = 'USB_ENCRYPTION_NOT_SUPPORTED'
    USB_DISK_ERROR = 'USB_DISK_ERROR'

    # Printer preflight related errors
    ERROR_PRINTER_NOT_FOUND = 'ERROR_PRINTER_NOT_FOUND'
    ERROR_PRINTER_NOT_SUPPORTED = 'ERROR_PRINTER_NOT_SUPPORTED'
    ERROR_PRINTER_DRIVER_UNAVAILABLE = 'ERROR_PRINTER_DRIVER_UNAVAILABLE'
    ERROR_PRINTER_INSTALL = 'ERROR_PRINTER_INSTALL'

    # Disk export errors
    USB_BAD_PASSPHRASE = 'USB_BAD_PASSPHRASE'
    ERROR_USB_MOUNT = 'ERROR_USB_MOUNT'
    ERROR_USB_WRITE = 'ERROR_USB_WRITE'

    # Printer export errors
    ERROR_PRINT = 'ERROR_PRINT'


class Metadata(object):
    """
    Object to parse, validate and store json metadata from the sd-export archive.
    """

    METADATA_FILE = "metadata.json"
    SUPPORTED_EXPORT_METHODS = [
        "usb-test",  # general preflight check
        "disk",
        "disk-test",  # disk preflight test
        "printer",
        "printer-test",  # print test page
    ]
    SUPPORTED_ENCRYPTION_METHODS = ["luks"]

    def __init__(self, archive_path):
        self.metadata_path = os.path.join(archive_path, self.METADATA_FILE)

        try:
            with open(self.metadata_path) as f:
                logging.info('Parsing archive metadata')
                json_config = json.loads(f.read())
                self.export_method = json_config.get("device", None)
                self.encryption_method = json_config.get("encryption_method", None)
                self.encryption_key = json_config.get(
                    "encryption_key", None
                )
                logging.info(
                    'Exporting to device {} with encryption_method {}'.format(
                        self.export_method, self.encryption_method
                    )
                )

        except Exception:
            logging.error('Metadata parsing failure')
            raise

    def is_valid(self):
        logging.info('Validating metadata contents')
        if self.export_method not in self.SUPPORTED_EXPORT_METHODS:
            logging.error(
                'Archive metadata: Export method {} is not supported'.format(
                    self.export_method
                )
            )
            return False

        if self.export_method == "disk":
            if self.encryption_method not in self.SUPPORTED_ENCRYPTION_METHODS:
                logging.error(
                    'Archive metadata: Encryption method {} is not supported'.format(
                        self.encryption_method
                    )
                )
                return False
        return True


class SDExport(object):
    def __init__(self, archive, config_path):
        self.device = DEVICE
        self.mountpoint = MOUNTPOINT
        self.encrypted_device = ENCRYPTED_DEVICE

        self.printer_name = PRINTER_NAME
        self.printer_wait_timeout = PRINTER_WAIT_TIMEOUT

        self.brlaser_driver = BRLASER_DRIVER
        self.brlaser_ppd = BRLASER_PPD

        self.archive = archive
        self.submission_dirname = os.path.basename(self.archive).split(".")[0]
        self.target_dirname = "sd-export-{}".format(
            datetime.datetime.now().strftime("%Y%m%d-%H%M%S")
        )
        self.tmpdir = tempfile.mkdtemp()

    def safe_check_call(self, command, error_message):
        """
        Safely wrap subprocess.check_output to ensure we always return 0 and
        log the error messages
        """
        try:
            subprocess.check_call(command)
        except subprocess.CalledProcessError as ex:
            self.exit_gracefully(msg=error_message, e=ex.output)

    def exit_gracefully(self, msg, e=False):
        """
        Utility to print error messages, mostly used during debugging,
        then exits successfully despite the error. Always exits 0,
        since non-zero exit values will cause system to try alternative
        solutions for mimetype handling, which we want to avoid.
        """
        logger.info('Exiting with message: {}'.format(msg))
        if not e:
            sys.stderr.write(msg)
            sys.stderr.write("\n")
        else:
            try:
                # If the file archive was extracted, delete before returning
                if os.path.isdir(self.tmpdir):
                    shutil.rmtree(self.tmpdir)
                logger.error("{}:{}".format(msg, e.output))
            except Exception as ex:
                logger.error("Unhandled exception: {}".format(ex))
                sys.stderr.write(ExportStatus.ERROR_GENERIC.value)
        # exit with 0 return code otherwise the os will attempt to open
        # the file with another application
        sys.exit(0)

    def popup_message(self, msg):
        self.safe_check_call(
            command=[
                "notify-send",
                "--expire-time",
                "3000",
                "--icon",
                "/usr/share/securedrop/icons/sd-logo.png",
                "SecureDrop: {}".format(msg),
            ],
            error_message="Error sending notification:"
        )

    def extract_tarball(self):
        try:
            logging.info('Extracting tarball {} into {}'.format(self.archive, self.tmpdir))
            with tarfile.open(self.archive) as tar:
                tar.extractall(self.tmpdir)
        except Exception:
            self.exit_gracefully(ExportStatus.ERROR_EXTRACTION.value)

    def check_usb_connected(self):
        # If the USB is not attached via qvm-usb attach, lsusb will return empty string and a
        # return code of 1
        logging.info('Performing usb preflight')
        try:
            subprocess.check_output(
                ["lsblk", "-p", "-o", "KNAME", "--noheadings", "--inverse", DEVICE],
                stderr=subprocess.PIPE)
            self.exit_gracefully(ExportStatus.USB_CONNECTED.value)
        except subprocess.CalledProcessError:
            self.exit_gracefully(ExportStatus.USB_NOT_CONNECTED.value)

    def set_extracted_device_name(self):
        try:
            device_and_partitions = subprocess.check_output(
                ["lsblk", "-o", "TYPE", "--noheadings", DEVICE], stderr=subprocess.PIPE)

            # we don't support multiple partitions
            partition_count = device_and_partitions.decode('utf-8').split('\n').count('part')
            if partition_count > 1:
                logging.debug("multiple partitions not supported")
                self.exit_gracefully(ExportStatus.USB_ENCRYPTION_NOT_SUPPORTED.value)

            # set device to /dev/sda if disk is encrypted, /dev/sda1 if partition encrypted
            self.device = DEVICE if partition_count == 0 else DEVICE + '1'
        except subprocess.CalledProcessError:
            self.exit_gracefully(ExportStatus.USB_ENCRYPTION_NOT_SUPPORTED.value)

    def check_luks_volume(self):
        # cryptsetup isLuks returns 0 if the device is a luks volume
        # subprocess with throw if the device is not luks (rc !=0)
        logging.info('Checking if volume is luks-encrypted')
        self.set_extracted_device_name()
        logging.debug("checking if {} is luks encrypted".format(self.device))
        self.safe_check_call(
            command=["sudo", "cryptsetup", "isLuks", self.device],
            error_message=ExportStatus.USB_ENCRYPTION_NOT_SUPPORTED.value
        )
        self.exit_gracefully(ExportStatus.USB_ENCRYPTED.value)

    def unlock_luks_volume(self, encryption_key):
        try:
            # get the encrypted device name
            self.set_extracted_device_name()
            luks_header = subprocess.check_output(["sudo", "cryptsetup", "luksDump", self.device])
            luks_header_list = luks_header.decode('utf-8').split('\n')
            for line in luks_header_list:
                items = line.split('\t')
                if 'UUID' in items[0]:
                    self.encrypted_device = 'luks-' + items[1]

            # the luks device is not already unlocked
            if not os.path.exists(os.path.join("/dev/mapper/", self.encrypted_device)):
                logging.debug('Unlocking luks volume {}'.format(self.encrypted_device))
                p = subprocess.Popen(
                    ["sudo", "cryptsetup", "luksOpen", self.device, self.encrypted_device],
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE
                )
                logging.debug('Passing key')
                p.communicate(input=str.encode(encryption_key, "utf-8"))
                rc = p.returncode
                if rc != 0:
                    logging.error('Bad phassphrase for {}'.format(self.encrypted_device))
                    self.exit_gracefully(ExportStatus.USB_BAD_PASSPHRASE.value)
        except subprocess.CalledProcessError:
            self.exit_gracefully(ExportStatus.USB_ENCRYPTION_NOT_SUPPORTED)

    def mount_volume(self):
        # mount target not created, create folder
        if not os.path.exists(self.mountpoint):
            self.safe_check_call(
                command=["sudo", "mkdir", self.mountpoint],
                error_message=ExportStatus.ERROR_USB_MOUNT
            )

        mapped_device_path = os.path.join("/dev/mapper/", self.encrypted_device)
        logging.info('Mounting {}'.format(mapped_device_path))
        self.safe_check_call(
            command=["sudo", "mount", mapped_device_path, self.mountpoint],
            error_message=ExportStatus.ERROR_USB_MOUNT.value
        )
        self.safe_check_call(
            command=["sudo", "chown", "-R", "user:user", self.mountpoint],
            error_message=ExportStatus.ERROR_USB_MOUNT.value
        )

    def copy_submission(self):
        # move files to drive (overwrites files with same filename) and unmount drive
        # we don't use safe_check_call here because we must lock and
        # unmount the drive as part of the finally block
        try:
            target_path = os.path.join(self.mountpoint, self.target_dirname)
            subprocess.check_call(["mkdir", target_path])
            export_data = os.path.join(self.tmpdir, "export_data/")
            logging.info('Copying file to {}'.format(self.target_dirname))
            subprocess.check_call(["cp", "-r", export_data, target_path])
            logging.info('File copied successfully to {}'.format(self.target_dirname))
            self.popup_message("Files exported successfully to disk.")
        except (subprocess.CalledProcessError, OSError):
            self.exit_gracefully(ExportStatus.ERROR_USB_WRITE.value)
        finally:
            # Finally, we sync the filesystem, unmount the drive and lock the
            # luks volume, and exit 0
            logging.info('Syncing filesystems')
            subprocess.check_call(["sync"])
            logging.info('Unmounting drive from {}'.format(self.mountpoint))
            subprocess.check_call(["sudo", "umount", self.mountpoint])
            logging.info('Locking luks volume {}'.format(self.encrypted_device))
            subprocess.check_call(
                ["sudo", "cryptsetup", "luksClose", self.encrypted_device]
            )
            logging.info('Deleting temporary directory {}'.format(self.tmpdir))
            subprocess.check_call(["rm", "-rf", self.tmpdir])
            sys.exit(0)

    def wait_for_print(self):
        # use lpstat to ensure the job was fully transfered to the printer
        # returns True if print was successful, otherwise will throw exceptions
        signal.signal(signal.SIGALRM, handler)
        signal.alarm(self.printer_wait_timeout)
        printer_idle_string = "printer {} is idle".format(self.printer_name)
        while True:
            try:
                logging.info('Running lpstat waiting for printer {}'.format(self.printer_name))
                output = subprocess.check_output(["lpstat", "-p", self.printer_name])
                if printer_idle_string in output.decode("utf-8"):
                    logging.info('Print completed')
                    return True
                else:
                    time.sleep(5)
            except subprocess.CalledProcessError:
                self.exit_gracefully(ExportStatus.ERROR_PRINT.value)
            except TimeoutException:
                logging.error('Timeout waiting for printer {}'.format(self.printer_name))
                self.exit_gracefully(ExportStatus.ERROR_PRINT.value)
        return True

    def get_printer_uri(self):
        # Get the URI via lpinfo and only accept URIs of supported printers
        printer_uri = ""
        try:
            output = subprocess.check_output(["sudo", "lpinfo", "-v"])
        except subprocess.CalledProcessError:
            self.exit_gracefully(ExportStatus.ERROR_PRINTER_URI.value)

        # fetch the usb printer uri
        for line in output.split():
            if "usb://" in line.decode("utf-8"):
                printer_uri = line.decode("utf-8")
                logging.info('lpinfo usb printer: {}'.format(printer_uri))

        # verify that the printer is supported, else exit
        if printer_uri == "":
            # No usb printer is connected
            logging.info('No usb printers connected')
            self.exit_gracefully(ExportStatus.ERROR_PRINTER_NOT_FOUND.value)
        elif "Brother" in printer_uri:
            logging.info('Printer {} is supported'.format(printer_uri))
            return printer_uri
        else:
            # printer url is a make that is unsupported
            logging.info('Printer {} is unsupported'.format(printer_uri))
            self.exit_gracefully(ExportStatus.ERROR_PRINTER_NOT_SUPPORTED.value)

    def install_printer_ppd(self, uri):
        # Some drivers don't come with ppd files pre-compiled, we must compile them
        if "Brother" in uri:
            self.safe_check_call(
                command=[
                    "sudo",
                    "ppdc",
                    self.brlaser_driver,
                    "-d",
                    "/usr/share/cups/model/",
                ],
                error_message=ExportStatus.ERROR_PRINTER_DRIVER_UNAVAILABLE.value
            )
            return self.brlaser_ppd
        # Here, we could support ppd drivers for other makes or models in the future

    def setup_printer(self, printer_uri, printer_ppd):
        # Add the printer using lpadmin
        self.safe_check_call(
            command=[
                "sudo",
                "lpadmin",
                "-p",
                self.printer_name,
                "-v",
                printer_uri,
                "-P",
                printer_ppd,
            ],
            error_message=ExportStatus.ERROR_PRINTER_INSTALL.value
        )
        # Activate the printer so that it can receive jobs
        self.safe_check_call(
            command=["sudo", "lpadmin", "-p", self.printer_name, "-E"],
            error_message=ExportStatus.ERROR_PRINTER_INSTALL.value
        )
        # Allow user to print (without using sudo)
        self.safe_check_call(
            command=["sudo", "lpadmin", "-p", self.printer_name, "-u", "allow:user"],
            error_message=ExportStatus.ERROR_PRINTER_INSTALL.value
        )

    def print_test_page(self):
        self.print_file("/usr/share/cups/data/testprint")
        self.popup_message("Printing test page")

    def print_all_files(self):
        files_path = os.path.join(self.tmpdir, "export_data/")
        files = os.listdir(files_path)
        print_count = 0
        for f in files:
            file_path = os.path.join(files_path, f)
            self.print_file(file_path)
            print_count += 1
            msg = "Printing document {} of {}".format(print_count, len(files))
            self.popup_message(msg)

    def is_open_office_file(self, filename):
        OPEN_OFFICE_FORMATS = [
            ".doc",
            ".docx",
            ".xls",
            ".xlsx",
            ".ppt",
            ".pptx",
            ".odt",
            ".ods",
            ".odp",
        ]
        for extension in OPEN_OFFICE_FORMATS:
            if os.path.basename(filename).endswith(extension):
                return True
        return False

    def print_file(self, file_to_print):
        # If the file to print is an (open)office document, we need to call unoconf to
        # convert the file to pdf as printer drivers do not support this format
        if self.is_open_office_file(file_to_print):
            logging.info('Converting Office document to pdf'.format(self.printer_name))
            folder = os.path.dirname(file_to_print)
            converted_filename = file_to_print + ".pdf"
            converted_path = os.path.join(folder, converted_filename)
            self.safe_check_call(
                command=["unoconv", "-o", converted_path, file_to_print],
                error_message=ExportStatus.ERROR_PRINT.value
            )
            file_to_print = converted_path

        logging.info('Sending file to printer {}:{}'.format(self.printer_name))
        self.safe_check_call(
            command=["xpp", "-P", self.printer_name, file_to_print],
            error_message=ExportStatus.ERROR_PRINT.value
        )


# class ends here
class TimeoutException(Exception):
    pass


def handler(s, f):
    raise TimeoutException("Timeout")
