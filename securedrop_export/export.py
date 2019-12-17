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
from typing import List, Optional  # noqa: F401

from securedrop_export.exceptions import ExportStatus, handler, TimeoutException

PRINTER_NAME = "sdw-printer"
PRINTER_WAIT_TIMEOUT = 60
MOUNTPOINT = "/media/usb"
ENCRYPTED_DEVICE = "encrypted_volume"
BRLASER_DRIVER = "/usr/share/cups/drv/brlaser.drv"
BRLASER_PPD = "/usr/share/cups/model/br7030.ppd"
LASERJET_DRIVER = "/usr/share/cups/drv/hpcups.drv"
LASERJET_PPD = "/usr/share/cups/model/hp-laserjet_6l.ppd"

logger = logging.getLogger(__name__)


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
                logger.info('Parsing archive metadata')
                json_config = json.loads(f.read())
                self.export_method = json_config.get("device", None)
                self.encryption_method = json_config.get("encryption_method", None)
                self.encryption_key = json_config.get(
                    "encryption_key", None
                )
                logger.info(
                    'Exporting to device {} with encryption_method {}'.format(
                        self.export_method, self.encryption_method
                    )
                )

        except Exception:
            logger.error('Metadata parsing failure')
            raise

    def is_valid(self):
        logger.info('Validating metadata contents')
        if self.export_method not in self.SUPPORTED_EXPORT_METHODS:
            logger.error(
                'Archive metadata: Export method {} is not supported'.format(
                    self.export_method
                )
            )
            return False

        if self.export_method == "disk":
            if self.encryption_method not in self.SUPPORTED_ENCRYPTION_METHODS:
                logger.error(
                    'Archive metadata: Encryption method {} is not supported'.format(
                        self.encryption_method
                    )
                )
                return False
        return True


class SDExport(object):
    def __init__(self, archive, config_path):
        self.device = None  # Optional[str]
        self.mountpoint = MOUNTPOINT
        self.encrypted_device = ENCRYPTED_DEVICE

        self.printer_name = PRINTER_NAME
        self.printer_wait_timeout = PRINTER_WAIT_TIMEOUT

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
            logger.info('Extracting tarball {} into {}'.format(self.archive, self.tmpdir))
            with tarfile.open(self.archive) as tar:
                tar.extractall(self.tmpdir)
        except Exception:
            self.exit_gracefully(ExportStatus.ERROR_EXTRACTION.value)

    def check_usb_connected(self, exit=False) -> None:
        usb_devices = self._get_connected_usbs()

        if len(usb_devices) == 0:
            logger.info('0 USB devices connected')
            self.exit_gracefully(ExportStatus.USB_NOT_CONNECTED.value)
        elif len(usb_devices) == 1:
            logger.info('1 USB device connected')
            self.device = usb_devices[0]
            if exit:
                self.exit_gracefully(ExportStatus.USB_CONNECTED.value)
        elif len(usb_devices) > 1:
            logger.info('>1 USB devices connected')
            # Return generic error until freedomofpress/securedrop-export/issues/25
            self.exit_gracefully(ExportStatus.ERROR_GENERIC.value)

    def _get_connected_usbs(self) -> List[str]:
        logger.info('Performing usb preflight')
        # List all block devices attached to VM that are disks and not partitions.
        try:
            lsblk = subprocess.Popen(["lsblk", "-o", "NAME,TYPE"], stdout=subprocess.PIPE,
                                     stderr=subprocess.PIPE)
            grep = subprocess.Popen(["grep", "disk"], stdin=lsblk.stdout, stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE)
            command_output = grep.stdout.readlines()

            # The first word in each element of the command_output list is the device name
            attached_devices = [x.decode('utf8').split()[0] for x in command_output]
        except subprocess.CalledProcessError:
            self.exit_gracefully(ExportStatus.ERROR_GENERIC.value)

        # Determine which are USBs by selecting those block devices that are removable disks.
        usb_devices = []
        for device in attached_devices:
            try:
                removable = subprocess.check_output(
                    ["cat", "/sys/class/block/{}/removable".format(device)],
                    stderr=subprocess.PIPE)
                is_removable = int(removable.decode('utf8').strip())
            except subprocess.CalledProcessError:
                is_removable = False

            if is_removable:
                usb_devices.append("/dev/{}".format(device))

        return usb_devices

    def set_extracted_device_name(self):
        try:
            device_and_partitions = subprocess.check_output(
                ["lsblk", "-o", "TYPE", "--noheadings", self.device], stderr=subprocess.PIPE)

            # we don't support multiple partitions
            partition_count = device_and_partitions.decode('utf-8').split('\n').count('part')
            if partition_count > 1:
                logger.debug("multiple partitions not supported")
                self.exit_gracefully(ExportStatus.USB_ENCRYPTION_NOT_SUPPORTED.value)

            # redefine device to /dev/sda if disk is encrypted, /dev/sda1 if partition encrypted
            self.device = self.device if partition_count == 0 else self.device + '1'
        except subprocess.CalledProcessError:
            self.exit_gracefully(ExportStatus.USB_ENCRYPTION_NOT_SUPPORTED.value)

    def check_luks_volume(self):
        # cryptsetup isLuks returns 0 if the device is a luks volume
        # subprocess with throw if the device is not luks (rc !=0)
        logger.info('Checking if volume is luks-encrypted')
        self.set_extracted_device_name()
        logger.debug("checking if {} is luks encrypted".format(self.device))
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

            # the luks device is already unlocked
            if os.path.exists(os.path.join('/dev/mapper/', self.encrypted_device)):
                logger.debug('Device already unlocked')
                return

            logger.debug('Unlocking luks volume {}'.format(self.encrypted_device))
            p = subprocess.Popen(
                ["sudo", "cryptsetup", "luksOpen", self.device, self.encrypted_device],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE
            )
            logger.debug('Passing key')
            p.communicate(input=str.encode(encryption_key, "utf-8"))
            rc = p.returncode
            if rc != 0:
                logger.error('Bad phassphrase for {}'.format(self.encrypted_device))
                self.exit_gracefully(ExportStatus.USB_BAD_PASSPHRASE.value)
        except subprocess.CalledProcessError:
            self.exit_gracefully(ExportStatus.USB_ENCRYPTION_NOT_SUPPORTED)

    def mount_volume(self):
        # If the drive is already mounted then we don't need to mount it again
        output = subprocess.check_output(
            ["lsblk", "-o", "MOUNTPOINT", "--noheadings", self.device])
        mountpoint = output.decode('utf-8').strip()
        if mountpoint:
            logger.debug('The device is already mounted')
            self.mountpoint = mountpoint
            return

        # mount target not created, create folder
        if not os.path.exists(self.mountpoint):
            self.safe_check_call(
                command=["sudo", "mkdir", self.mountpoint],
                error_message=ExportStatus.ERROR_USB_MOUNT
            )

        mapped_device_path = os.path.join("/dev/mapper/", self.encrypted_device)
        logger.info('Mounting {}'.format(mapped_device_path))
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
            logger.info('Copying file to {}'.format(self.target_dirname))
            subprocess.check_call(["cp", "-r", export_data, target_path])
            logger.info('File copied successfully to {}'.format(self.target_dirname))
            self.popup_message("Files exported successfully to disk.")
        except (subprocess.CalledProcessError, OSError):
            self.exit_gracefully(ExportStatus.ERROR_USB_WRITE.value)
        finally:
            logger.info('Syncing filesystems')
            subprocess.check_call(["sync"])

            if os.path.exists(self.mountpoint):
                logger.info('Unmounting drive from {}'.format(self.mountpoint))
                subprocess.check_call(["sudo", "umount", self.mountpoint])

            if os.path.exists(os.path.join('/dev/mapper', self.encrypted_device)):
                logger.info('Locking luks volume {}'.format(self.encrypted_device))
                subprocess.check_call(
                    ["sudo", "cryptsetup", "luksClose", self.encrypted_device]
                )

            logger.info('Deleting temporary directory {}'.format(self.tmpdir))
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
                logger.info('Running lpstat waiting for printer {}'.format(self.printer_name))
                output = subprocess.check_output(["lpstat", "-p", self.printer_name])
                if printer_idle_string in output.decode("utf-8"):
                    logger.info('Print completed')
                    return True
                else:
                    time.sleep(5)
            except subprocess.CalledProcessError:
                self.exit_gracefully(ExportStatus.ERROR_PRINT.value)
            except TimeoutException:
                logger.error('Timeout waiting for printer {}'.format(self.printer_name))
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
                logger.info('lpinfo usb printer: {}'.format(printer_uri))

        # verify that the printer is supported, else exit
        if printer_uri == "":
            # No usb printer is connected
            logger.info('No usb printers connected')
            self.exit_gracefully(ExportStatus.ERROR_PRINTER_NOT_FOUND.value)
        elif not any(x in printer_uri for x in ("Brother", "LaserJet")):
            # printer url is a make that is unsupported
            logger.info('Printer {} is unsupported'.format(printer_uri))
            self.exit_gracefully(ExportStatus.ERROR_PRINTER_NOT_SUPPORTED.value)

        logger.info('Printer {} is supported'.format(printer_uri))
        return printer_uri

    def install_printer_ppd(self, uri):
        if not any(x in uri for x in ("Brother", "LaserJet")):
            logger.error("Cannot install printer ppd for unsupported printer: {}".format(uri))
            self.exit_gracefully(msg=ExportStatus.ERROR_PRINTER_NOT_SUPPORTED.value)
            return

        if "Brother" in uri:
            printer_driver = BRLASER_DRIVER
            printer_ppd = BRLASER_PPD
        elif "LaserJet" in uri:
            printer_driver = LASERJET_DRIVER
            printer_ppd = LASERJET_PPD

        # Some drivers don't come with ppd files pre-compiled, we must compile them
        self.safe_check_call(
            command=[
                "sudo",
                "ppdc",
                printer_driver,
                "-d",
                "/usr/share/cups/model/",
            ],
            error_message=ExportStatus.ERROR_PRINTER_DRIVER_UNAVAILABLE.value
        )
        return printer_ppd

    def setup_printer(self, printer_uri, printer_ppd):
        # Add the printer using lpadmin
        logger.info('Setting up printer name {}'.format(self.printer_name))
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
        logger.info('Activating printer {}'.format(self.printer_name))
        self.safe_check_call(
            command=["sudo", "lpadmin", "-p", self.printer_name],
            error_message=ExportStatus.ERROR_PRINTER_INSTALL.value
        )
        # worksaround for version of lpadmin/cups in debian buster:
        # see https://forums.developer.apple.com/thread/106112
        self.safe_check_call(
            command=["sudo", "cupsaccept", self.printer_name],
            error_message=ExportStatus.ERROR_PRINTER_INSTALL.value
        )
        # A non-zero return code is expected here, but the command is required
        # and works as expected.
        command = ["sudo", "cupsenable", self.printer_name]
        try:
            subprocess.check_call(command)
        except subprocess.CalledProcessError:
            pass

        # Allow user to print (without using sudo)
        logger.info('Allow user to print {}'.format(self.printer_name))
        self.safe_check_call(
            command=["sudo", "lpadmin", "-p", self.printer_name, "-u", "allow:user"],
            error_message=ExportStatus.ERROR_PRINTER_INSTALL.value
        )

    def print_test_page(self):
        logger.info('Printing test page')
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
            logger.info('Converting Office document to pdf')
            folder = os.path.dirname(file_to_print)
            converted_filename = file_to_print + ".pdf"
            converted_path = os.path.join(folder, converted_filename)
            self.safe_check_call(
                command=["unoconv", "-o", converted_path, file_to_print],
                error_message=ExportStatus.ERROR_PRINT.value
            )
            file_to_print = converted_path

        logger.info('Sending file to printer {}:{}'.format(self.printer_name, file_to_print))
        self.safe_check_call(
            command=["xpp", "-P", self.printer_name, file_to_print],
            error_message=ExportStatus.ERROR_PRINT.value
        )
