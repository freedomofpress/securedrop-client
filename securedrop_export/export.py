#!/usr/bin/env python3

import datetime
import json
import os
import shutil
import signal
import subprocess
import sys
import tarfile
import tempfile
import time

PRINTER_NAME = "sdw-printer"
PRINTER_WAIT_TIMEOUT = 60
DEVICE = "/dev/sda1"
MOUNTPOINT = "/media/usb"
ENCRYPTED_DEVICE = "encrypted_volume"
BRLASER_DRIVER = "/usr/share/cups/drv/brlaser.drv"
BRLASER_PPD = "/usr/share/cups/model/br7030.ppd"


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
                json_config = json.loads(f.read())
                self.export_method = json_config.get("device", None)
                self.encryption_method = json_config.get("encryption_method", None)
                self.encryption_key = json_config.get("encryption_key", None)

        except Exception:
            raise

    def is_valid(self):
        if self.export_method not in self.SUPPORTED_EXPORT_METHODS:
            return False

        if self.export_method == "disk":
            if self.encryption_method not in self.SUPPORTED_ENCRYPTION_METHODS:
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

        try:
            with open(config_path) as f:
                json_config = json.loads(f.read())
                self.pci_bus_id = int(json_config.get("pci_bus_id", 2))
        except Exception:
            self.exit_gracefully("ERROR_CONFIG")

    def exit_gracefully(self, msg, e=False):
        """
        Utility to print error messages, mostly used during debugging,
        then exits successfully despite the error. Always exits 0,
        since non-zero exit values will cause system to try alternative
        solutions for mimetype handling, which we want to avoid.
        """
        sys.stderr.write(msg)
        sys.stderr.write("\n")
        if e:
            try:
                # If the file archive was extracted, delete before returning
                if os.path.isdir(self.tmpdir):
                    shutil.rmtree(self.tmpdir)
                e_output = e.output
            except Exception:
                e_output = "<unknown exception>"
            sys.stderr.write(e_output)
            sys.stderr.write("\n")
        # exit with 0 return code otherwise the os will attempt to open
        # the file with another application
        sys.exit(0)

    def popup_message(self, msg):
        try:
            subprocess.check_call(
                [
                    "notify-send",
                    "--expire-time",
                    "3000",
                    "--icon",
                    "/usr/share/securedrop/icons/sd-logo.png",
                    "SecureDrop: {}".format(msg),
                ]
            )
        except subprocess.CalledProcessError as e:
            msg = "Error sending notification:"
            self.exit_gracefully(msg, e=e)

    def extract_tarball(self):
        try:
            with tarfile.open(self.archive) as tar:
                tar.extractall(self.tmpdir)
        except Exception:
            msg = "ERROR_EXTRACTION"
            self.exit_gracefully(msg)

    def check_usb_connected(self):
        p = subprocess.check_output(["lsusb", "-s", self.pci_bus_id])
        # Empty string means a likely wrong pci_bus_id
        if p == "":
            msg = "ERROR_USB_CHECK"
            self.exit_gracefully(msg)
        n_usb = len(p.rstrip().split("\n"))
        # If there is one device, it is the root hub.
        if n_usb == 1:
            msg = "USB_NOT_CONNECTED"
            self.exit_gracefully(msg)
        # If there are two devices, it's the root hub and another device (presumably for export)
        elif n_usb == 2:
            msg = "USB_CONNECTED"
            self.exit_gracefully(msg)
        # Else the result is unexpected
        else:
            msg = "ERROR_USB_CHECK"
            self.exit_gracefully(msg)

    def check_luks_volume(self):
        try:
            # cryptsetup isLuks returns 0 if the device is a luks volume
            # subprocess with throw if the device is not luks (rc !=0)
            p = subprocess.check_call(["sudo", "cryptsetup", "isLuks", DEVICE])
            msg = "USB_ENCRYPTED"
            self.exit_gracefully(msg)
        except subprocess.CalledProcessError:
            msg = "USB_NO_SUPPORTED_ENCRYPTION"
            self.exit_gracefully(msg)

    def unlock_luks_volume(self, encryption_key):
        # the luks device is not already unlocked
        if not os.path.exists(os.path.join("/dev/mapper/", self.encrypted_device)):
            p = subprocess.Popen(
                ["sudo", "cryptsetup", "luksOpen", self.device, self.encrypted_device],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            p.communicate(input=str.encode(encryption_key, "utf-8"))
            rc = p.returncode
            if rc != 0:
                msg = "USB_BAD_PASSPHRASE"
                self.exit_gracefully(msg)

    def mount_volume(self):
        # mount target not created
        if not os.path.exists(self.mountpoint):
            subprocess.check_call(["sudo", "mkdir", self.mountpoint])
        try:
            subprocess.check_call(
                [
                    "sudo",
                    "mount",
                    os.path.join("/dev/mapper/", self.encrypted_device),
                    self.mountpoint,
                ]
            )
            subprocess.check_call(["sudo", "chown", "-R", "user:user", self.mountpoint])
        except subprocess.CalledProcessError:
            # clean up
            subprocess.check_call(
                ["sudo", "cryptsetup", "luksClose", self.encrypted_device]
            )
            msg = "ERROR_USB_MOUNT"
            self.exit_gracefully(msg)

    def copy_submission(self):
        # move files to drive (overwrites files with same filename) and unmount drive
        try:
            target_path = os.path.join(self.mountpoint, self.target_dirname)
            subprocess.check_call(["mkdir", target_path])
            export_data = os.path.join(self.tmpdir, "export_data/")
            subprocess.check_call(["cp", "-r", export_data, target_path])
            self.popup_message("Files exported successfully to disk.")
        except (subprocess.CalledProcessError, OSError):
            msg = "ERROR_USB_WRITE"
            self.exit_gracefully(msg)
        finally:
            # Finally, we sync the filesystem, unmount the drive and lock the
            # luks volume, and exit 0
            subprocess.check_call(["sync"])
            subprocess.check_call(["sudo", "umount", self.mountpoint])
            subprocess.check_call(
                ["sudo", "cryptsetup", "luksClose", self.encrypted_device]
            )
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
                output = subprocess.check_output(["lpstat", "-p", self.printer_name])
                if printer_idle_string in output.decode("utf-8"):
                    return True
                else:
                    time.sleep(5)
            except subprocess.CalledProcessError:
                msg = "ERROR_PRINT"
                self.exit_gracefully(msg)
            except TimeoutException:
                msg = "ERROR_PRINT"
                self.exit_gracefully(msg)
        return True

    def get_printer_uri(self):
        # Get the URI via lpinfo and only accept URIs of supported printers
        printer_uri = ""
        try:
            output = subprocess.check_output(["sudo", "lpinfo", "-v"])
        except subprocess.CalledProcessError:
            msg = "ERROR_PRINTER_URI"
            self.exit_gracefully(msg)

        # fetch the usb printer uri
        for line in output.split():
            if "usb://" in line.decode("utf-8"):
                printer_uri = line.decode("utf-8")

        # verify that the printer is supported, else exit
        if printer_uri == "":
            # No usb printer is connected
            self.exit_gracefully("ERROR_PRINTER_NOT_FOUND")
        elif "Brother" in printer_uri:
            return printer_uri
        else:
            # printer url is a make that is unsupported
            self.exit_gracefully("ERROR_PRINTER_NOT_SUPPORTED")

    def install_printer_ppd(self, uri):
        # Some drivers don't come with ppd files pre-compiled, we must compile them
        if "Brother" in uri:
            try:
                subprocess.check_call(
                    [
                        "sudo",
                        "ppdc",
                        self.brlaser_driver,
                        "-d",
                        "/usr/share/cups/model/",
                    ]
                )
            except subprocess.CalledProcessError:
                msg = "ERROR_PRINTER_DRIVER_INSTALL"
                self.exit_gracefully(msg)
            return self.brlaser_ppd
        # Here, we could support ppd drivers for other makes or models in the future

    def setup_printer(self, printer_uri, printer_ppd):
        try:
            # Add the printer using lpadmin
            subprocess.check_call(
                [
                    "sudo",
                    "lpadmin",
                    "-p",
                    self.printer_name,
                    "-v",
                    printer_uri,
                    "-P",
                    printer_ppd,
                ]
            )
            # Activate the printer so that it can receive jobs
            subprocess.check_call(["sudo", "lpadmin", "-p", self.printer_name, "-E"])
            # Allow user to print (without using sudo)
            subprocess.check_call(
                ["sudo", "lpadmin", "-p", self.printer_name, "-u", "allow:user"]
            )
        except subprocess.CalledProcessError:
            msg = "ERROR_PRINTER_INSTALL"
            self.exit_gracefully(msg)

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
        try:
            # if the file to print is an (open)office document, we need to call unoconf to convert
            # the file to pdf as printer drivers do not immediately support this format out of the box
            if self.is_open_office_file(file_to_print):
                folder = os.path.dirname(file_to_print)
                converted_filename = file_to_print + ".pdf"
                converted_path = os.path.join(folder, converted_filename)
                subprocess.check_call(["unoconv", "-o", converted_path, file_to_print])
                file_to_print = converted_path

            subprocess.check_call(["xpp", "-P", self.printer_name, file_to_print])
        except subprocess.CalledProcessError:
            msg = "ERROR_PRINT"
            self.exit_gracefully(msg)


## class ends here
class TimeoutException(Exception):
    pass


def handler(s, f):
    raise TimeoutException("Timeout")
