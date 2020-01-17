import logging
import os
import signal
import subprocess
import time

from securedrop_export.exceptions import ExportStatus, handler, TimeoutException
from securedrop_export.export import ExportAction


PRINTER_NAME = "sdw-printer"
PRINTER_WAIT_TIMEOUT = 60
BRLASER_DRIVER = "/usr/share/cups/drv/brlaser.drv"
BRLASER_PPD = "/usr/share/cups/model/br7030.ppd"
LASERJET_DRIVER = "/usr/share/cups/drv/hpcups.drv"
LASERJET_PPD = "/usr/share/cups/model/hp-laserjet_6l.ppd"

logger = logging.getLogger(__name__)


class PrintAction(ExportAction):
    def __init__(self, submission):
        self.submission = submission
        self.printer_name = PRINTER_NAME
        self.printer_wait_timeout = PRINTER_WAIT_TIMEOUT

    def run(self) -> None:
        """Run logic"""
        raise NotImplementedError

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
                self.submission.exit_gracefully(ExportStatus.ERROR_PRINT.value)
            except TimeoutException:
                logger.error('Timeout waiting for printer {}'.format(self.printer_name))
                self.submission.exit_gracefully(ExportStatus.ERROR_PRINT.value)
        return True

    def check_printer_setup(self) -> None:
        try:
            logger.info('Searching for printer')
            output = subprocess.check_output(["sudo", "lpinfo", "-v"])
            printers = [x for x in output.decode('utf-8').split() if "usb://" in x]
            if not printers:
                logger.info('No usb printers connected')
                self.submission.exit_gracefully(ExportStatus.ERROR_PRINTER_NOT_FOUND.value)

            supported_printers = \
                [p for p in printers if any(sub in p for sub in ("Brother", "LaserJet"))]
            if not supported_printers:
                logger.info('{} are unsupported printers'.format(printers))
                self.submission.exit_gracefully(ExportStatus.ERROR_PRINTER_NOT_SUPPORTED.value)

            if len(supported_printers) > 1:
                logger.info('Too many usb printers connected')
                self.submission.exit_gracefully(ExportStatus.ERROR_MULTIPLE_PRINTERS_FOUND.value)

            printer_uri = printers[0]

            logger.info('Installing printer drivers')
            printer_ppd = self.install_printer_ppd(printer_uri)

            logger.info('Setting up printer')
            self.setup_printer(printer_uri, printer_ppd)
        except subprocess.CalledProcessError as e:
            logger.error(e)
            self.submission.exit_gracefully(ExportStatus.ERROR_GENERIC.value)

    def get_printer_uri(self):
        # Get the URI via lpinfo and only accept URIs of supported printers
        printer_uri = ""
        try:
            output = subprocess.check_output(["sudo", "lpinfo", "-v"])
        except subprocess.CalledProcessError:
            self.submission.exit_gracefully(ExportStatus.ERROR_PRINTER_URI.value)

        # fetch the usb printer uri
        for line in output.split():
            if "usb://" in line.decode("utf-8"):
                printer_uri = line.decode("utf-8")
                logger.info('lpinfo usb printer: {}'.format(printer_uri))

        # verify that the printer is supported, else exit
        if printer_uri == "":
            # No usb printer is connected
            logger.info('No usb printers connected')
            self.submission.exit_gracefully(ExportStatus.ERROR_PRINTER_NOT_FOUND.value)
        elif not any(x in printer_uri for x in ("Brother", "LaserJet")):
            # printer url is a make that is unsupported
            logger.info('Printer {} is unsupported'.format(printer_uri))
            self.submission.exit_gracefully(ExportStatus.ERROR_PRINTER_NOT_SUPPORTED.value)

        logger.info('Printer {} is supported'.format(printer_uri))
        return printer_uri

    def install_printer_ppd(self, uri):
        if not any(x in uri for x in ("Brother", "LaserJet")):
            logger.error("Cannot install printer ppd for unsupported printer: {}".format(uri))
            self.submission.exit_gracefully(msg=ExportStatus.ERROR_PRINTER_NOT_SUPPORTED.value)
            return

        if "Brother" in uri:
            printer_driver = BRLASER_DRIVER
            printer_ppd = BRLASER_PPD
        elif "LaserJet" in uri:
            printer_driver = LASERJET_DRIVER
            printer_ppd = LASERJET_PPD

        # Compile and install drivers that are not already installed
        if not os.path.exists(printer_ppd):
            self.submission.safe_check_call(
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
        self.submission.safe_check_call(
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
        self.submission.safe_check_call(
            command=["sudo", "lpadmin", "-p", self.printer_name],
            error_message=ExportStatus.ERROR_PRINTER_INSTALL.value
        )
        # worksaround for version of lpadmin/cups in debian buster:
        # see https://forums.developer.apple.com/thread/106112
        self.submission.safe_check_call(
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
        self.submission.safe_check_call(
            command=["sudo", "lpadmin", "-p", self.printer_name, "-u", "allow:user"],
            error_message=ExportStatus.ERROR_PRINTER_INSTALL.value
        )

    def print_test_page(self):
        logger.info('Printing test page')
        self.print_file("/usr/share/cups/data/testprint")

    def print_all_files(self):
        files_path = os.path.join(self.submission.tmpdir, "export_data/")
        files = os.listdir(files_path)
        print_count = 0
        for f in files:
            file_path = os.path.join(files_path, f)
            self.print_file(file_path)
            print_count += 1
            logger.info("Printing document {} of {}".format(print_count, len(files)))

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
            self.submission.safe_check_call(
                command=["unoconv", "-o", converted_path, file_to_print],
                error_message=ExportStatus.ERROR_PRINT.value
            )
            file_to_print = converted_path

        logger.info('Sending file to printer {}:{}'.format(self.printer_name, file_to_print))
        self.submission.safe_check_call(
            command=["xpp", "-P", self.printer_name, file_to_print],
            error_message=ExportStatus.ERROR_PRINT.value
        )


class PrintExportAction(PrintAction):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def run(self):
        logger.info('Export archive is printer')
        self.check_printer_setup()
        # prints all documents in the archive
        self.print_all_files()


class PrintTestPageAction(PrintAction):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def run(self):
        logger.info('Export archive is printer-test')
        self.check_printer_setup()
        # Prints a test page to ensure the printer is functional
        self.print_test_page()


class PrintPreflightAction(PrintAction):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def run(self):
        logger.info('Export archive is printer-preflight')
        self.check_printer_setup()
