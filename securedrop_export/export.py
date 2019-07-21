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
    SUPPORTED_EXPORT_METHODS = ["disk", "printer", "printer-test"]
    SUPPORTED_ENCRYPTION_METHODS = ["luks"]

    def __init__(self, archive_path):
        self.metadata_path = os.path.join(archive_path, self.METADATA_FILE)
        try:
            with open(self.metadata_path) as f:
                json_config = json.loads(f.read())
                self.export_method = json_config.get("device", None)
                self.encryption_method = json_config.get("encryption_method", None)
                self.encryption_key = json_config.get("encryption_key", None)
        except Exception as e:
            raise

    def is_valid(self):
        if self.export_method not in self.SUPPORTED_EXPORT_METHODS:
            return False

        if self.export_method == "disk":
            if self.encryption_method not in self.SUPPORTED_ENCRYPTION_METHODS:
                return False
        return True


class SDExport(object):

    def __init__(self, archive):
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
        self.popup_message("Export error: {}".format(msg))
        sys.exit(0)


    def popup_message(self, msg):
        try:
            subprocess.check_call([
                "notify-send",
                "--expire-time", "3000",
                "--icon", "/usr/share/securedrop/icons/sd-logo.png",
                "SecureDrop: {}".format(msg)
            ])
        except subprocess.CalledProcessError as e:
            msg = "Error sending notification:"
            self.exit_gracefully(msg, e=e)


    def extract_tarball(self):
        try:
            with tarfile.open(self.archive) as tar:
                tar.extractall(self.tmpdir)
        except Exception as e:
            print (e)
            msg = "Error opening export bundle: "
            self.exit_gracefully(msg, e=e)


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
                msg = "Bad passphrase or luks error."
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
            subprocess.check_call(
                [
                    "sudo", 
                    "chown", 
                    "-R", "user:user", self.mountpoint,
                ]
            )
        except subprocess.CalledProcessError as e:
            # clean up
            subprocess.check_call(["sudo", "cryptsetup", "luksClose", self.encrypted_device])
            msg = "An error occurred while mounting disk: "
            self.exit_gracefully(msg, e=e)


    def copy_submission(self):
        # move files to drive (overwrites files with same filename) and unmount drive
        try:
            target_path = os.path.join(self.mountpoint, self.target_dirname)
            subprocess.check_call(["mkdir", target_path])
            export_data = os.path.join(
                self.tmpdir, self.submission_dirname, "export_data/"
            )
            subprocess.check_call(["cp", "-r", export_data, target_path])
            self.popup_message("Files exported successfully to disk.")
        except (subprocess.CalledProcessError, OSError) as e:
            msg = "Error writing to disk:"
            self.exit_gracefully(msg, e=e)
        finally:
            # Finally, we sync the filesystem, unmount the drive and lock the
            # luks volume, and exit 0
            subprocess.check_call(["sync"])
            subprocess.check_call(["sudo", "umount", self.mountpoint])
            subprocess.check_call(["sudo", "cryptsetup", "luksClose", self.encrypted_device])
            subprocess.check_call(["rm", "-rf", self.tmpdir])
            sys.exit(0)


    def wait_for_print(self):
        # use lpstat to ensure the job was fully transfered to the printer
        # returns True if print was successful, otherwise will throw exceptions
        signal.signal(signal.SIGALRM, handler)
        signal.alarm(self.printer_wait_timeout)
        printer_idle_string = "printer {} is idle".format(self.printer_name)
        while(True):
            try:
                output = subprocess.check_output(["lpstat", "-p", self.printer_name])
                if(printer_idle_string in output.decode("utf-8")):
                    return True
                else:
                    time.sleep(5)
            except subprocess.CalledProcessError as e:
                msg = "Error while retrieving print status"
                self.exit_gracefully(msg, e=e)
            except TimeoutException as e:
                msg = "Timeout when getting printer information"
                self.exit_gracefully(msg, e=e)
        return True


    def get_printer_uri(self):
        # Get the URI via lpinfo and only accept URIs of supported printers
        printer_uri = ""
        try:
            output = subprocess.check_output(["sudo", "lpinfo", "-v"])
        except subprocess.CalledProcessError as e:
            msg = "Error retrieving printer uri."
            self.exit_gracefully(msg, e=e)

        # fetch the usb printer uri
        for line in output.split():
            if "usb://" in line.decode("utf-8"):
                printer_uri = line.decode("utf-8")

        # verify that the printer is supported, else exit
        if printer_uri == "":
            # No usb printer is connected
            self.exit_gracefully("USB Printer not found")
        elif "Brother" in printer_uri:
            return printer_uri
        else:
            # printer url is a make that is unsupported
            self.exit_gracefully("USB Printer not supported")


    def install_printer_ppd(self, uri):
         # Some drivers don't come with ppd files pre-compiled, we must compile them
        if "Brother" in uri:
            try:
                subprocess.check_call(
                    ["sudo", "ppdc", self.brlaser_driver, "-d", "/usr/share/cups/model/"]
                )
            except subprocess.CalledProcessError as e:
                msg = "Error installing ppd file for printer {}.".format(uri)
                self.exit_gracefully(msg, e=e)
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
        except subprocess.CalledProcessError as e:
            msg = "Error setting up printer {} at {} using {}.".format(
                self.printer_name, printer_uri, printer_ppd
            )
            self.exit_gracefully(msg, e=e)


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
        OPEN_OFFICE_FORMATS = [".doc", ".docx", ".xls", ".xlsx",
                               ".ppt", ".pptx", ".odt", ".ods", ".odp"]
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
        except subprocess.CalledProcessError as e:
            msg = "Error printing file {} with printer {}.".format(
                file_to_print, self.printer_name
            )
            self.exit_gracefully(msg, e=e)

## class ends here
class TimeoutException(Exception):
    pass


def handler(s, f):
    raise TimeoutException("Timeout")
