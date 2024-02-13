import logging
import os
import signal
import subprocess
import time

from securedrop_export.exceptions import ExportException, TimeoutException, handler

from .status import Status

logger = logging.getLogger(__name__)


class Service:
    """
    Printer service
    """

    PRINTER_NAME = "sdw-printer"
    PRINTER_WAIT_TIMEOUT = 60
    BRLASER_DRIVER = "/usr/share/cups/drv/brlaser.drv"
    BRLASER_PPD = "/usr/share/cups/model/br7030.ppd"
    LASERJET_DRIVER = "/usr/share/cups/drv/hpcups.drv"
    LASERJET_PPD = "/usr/share/cups/model/hp-laserjet_6l.ppd"

    BROTHER = "Brother"
    LASERJET = "LaserJet"

    SUPPORTED_PRINTERS = [BROTHER, LASERJET]

    def __init__(self, submission, printer_timeout_seconds=PRINTER_WAIT_TIMEOUT):
        self.submission = submission
        self.printer_name = self.PRINTER_NAME
        self.printer_wait_timeout = printer_timeout_seconds  # Override during testing

    def print(self) -> Status:
        """
        Routine to print all files.
        Throws ExportException if an error is encountered.
        """
        logger.info("Printing all files from archive")
        self._check_printer_setup()
        self._print_all_files()
        # When client can accept new print statuses, we will return
        # a success status here
        return Status.PRINT_SUCCESS

    def printer_preflight(self) -> Status:
        """
        Routine to perform preflight printer testing.

        Throws ExportException if an error is encoutered.
        """
        logger.info("Running printer preflight")
        self._check_printer_setup()
        # When client can accept new print statuses, we will return
        # a success status here
        return Status.PREFLIGHT_SUCCESS

    def printer_test(self) -> Status:
        """
        Routine to print a test page.

        Throws ExportException if an error is encountered.
        """
        logger.info("Printing test page")
        self._check_printer_setup()
        self._print_test_page()
        # When client can accept new print statuses, we will return
        # a success status here
        return Status.PRINT_TEST_PAGE_SUCCESS

    def _wait_for_print(self):
        """
        Use lpstat to ensure the job was fully transfered to the printer
        Return True if print was successful, otherwise throw ExportException.
        Currently, the handler `handler` is defined in `exceptions.py`.
        """
        signal.signal(signal.SIGALRM, handler)
        signal.alarm(self.printer_wait_timeout)
        printer_idle_string = "printer {} is idle".format(self.printer_name)
        while True:
            try:
                logger.info(
                    "Running lpstat waiting for printer {}".format(self.printer_name)
                )
                output = subprocess.check_output(["lpstat", "-p", self.printer_name])
                if printer_idle_string in output.decode("utf-8"):
                    logger.info("Print completed")
                    return True
                else:
                    time.sleep(5)
            except subprocess.CalledProcessError:
                raise ExportException(sdstatus=Status.ERROR_PRINT)
            except TimeoutException:
                logger.error("Timeout waiting for printer {}".format(self.printer_name))
                raise ExportException(sdstatus=Status.ERROR_PRINT)
        return True

    def _check_printer_setup(self) -> None:
        """
        Check printer setup.
        Raise ExportException if supported setup is not found.
        """
        try:
            logger.info("Searching for printer")
            output = subprocess.check_output(["sudo", "lpinfo", "-v"])
            printers = [x for x in output.decode("utf-8").split() if "usb://" in x]
            if not printers:
                logger.info("No usb printers connected")
                raise ExportException(sdstatus=Status.ERROR_PRINTER_NOT_FOUND)

            supported_printers = [
                p for p in printers if any(sub in p for sub in self.SUPPORTED_PRINTERS)
            ]
            if not supported_printers:
                logger.info("{} are unsupported printers".format(printers))
                raise ExportException(sdstatus=Status.ERROR_PRINTER_NOT_SUPPORTED)

            if len(supported_printers) > 1:
                logger.info("Too many usb printers connected")
                raise ExportException(sdstatus=Status.ERROR_MULTIPLE_PRINTERS_FOUND)

            printer_uri = printers[0]
            printer_ppd = self._install_printer_ppd(printer_uri)
            self._setup_printer(printer_uri, printer_ppd)
        except subprocess.CalledProcessError as e:
            logger.error(e)
            raise ExportException(sdstatus=Status.ERROR_UNKNOWN)

    def _get_printer_uri(self) -> str:
        """
        Get the URI via lpinfo. Only accept URIs of supported printers.

        Raise ExportException if supported setup is not found.
        """
        printer_uri = ""
        try:
            output = subprocess.check_output(["sudo", "lpinfo", "-v"])
        except subprocess.CalledProcessError:
            logger.error("Error attempting to retrieve printer uri with lpinfo")
            raise ExportException(sdstatus=Status.ERROR_PRINTER_URI)

        # fetch the usb printer uri
        for line in output.split():
            if "usb://" in line.decode("utf-8"):
                printer_uri = line.decode("utf-8")
                logger.info("lpinfo usb printer: {}".format(printer_uri))

        # verify that the printer is supported, else throw
        if printer_uri == "":
            # No usb printer is connected
            logger.info("No usb printers connected")
            raise ExportException(sdstatus=Status.ERROR_PRINTER_NOT_FOUND)
        elif not any(x in printer_uri for x in self.SUPPORTED_PRINTERS):
            # printer url is a make that is unsupported
            logger.info("Printer {} is unsupported".format(printer_uri))
            raise ExportException(sdstatus=Status.ERROR_PRINTER_NOT_SUPPORTED)

        logger.info("Printer {} is supported".format(printer_uri))
        return printer_uri

    def _install_printer_ppd(self, uri):
        if not any(x in uri for x in self.SUPPORTED_PRINTERS):
            logger.error(
                "Cannot install printer ppd for unsupported printer: {}".format(uri)
            )
            raise ExportException(sdstatus=Status.ERROR_PRINTER_NOT_SUPPORTED)

        if self.BROTHER in uri:
            printer_driver = self.BRLASER_DRIVER
            printer_ppd = self.BRLASER_PPD
        elif self.LASERJET in uri:
            printer_driver = self.LASERJET_DRIVER
            printer_ppd = self.LASERJET_PPD

        # Compile and install drivers that are not already installed
        if not os.path.exists(printer_ppd):
            logger.info("Installing printer drivers")
            self.safe_check_call(
                command=[
                    "sudo",
                    "ppdc",
                    printer_driver,
                    "-d",
                    "/usr/share/cups/model/",
                ],
                error_status=Status.ERROR_PRINTER_DRIVER_UNAVAILABLE,
                ignore_stderr_startswith=b"ppdc: Warning",
            )

        return printer_ppd

    def _setup_printer(self, printer_uri, printer_ppd):
        # Add the printer using lpadmin
        logger.info("Setting up printer {}".format(self.printer_name))
        self.safe_check_call(
            command=[
                "sudo",
                "lpadmin",
                "-p",
                self.printer_name,
                "-E",
                "-v",
                printer_uri,
                "-P",
                printer_ppd,
                "-u",
                "allow:user",
            ],
            error_status=Status.ERROR_PRINTER_INSTALL,
            ignore_stderr_startswith=b"lpadmin: Printer drivers",
        )

    def _print_test_page(self):
        logger.info("Printing test page")
        self._print_file("/usr/share/cups/data/testprint")

    def _print_all_files(self):
        files_path = os.path.join(self.submission.tmpdir, "export_data/")
        files = os.listdir(files_path)
        print_count = 0
        for f in files:
            file_path = os.path.join(files_path, f)
            self._print_file(file_path)
            print_count += 1
            logger.info("Printing document {} of {}".format(print_count, len(files)))

    def _is_open_office_file(self, filename):
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
            ".rtf",
        ]
        for extension in OPEN_OFFICE_FORMATS:
            if os.path.basename(filename).endswith(extension):
                return True
        return False

    def _print_file(self, file_to_print):
        # If the file to print is an (open)office document, we need to call unoconf to
        # convert the file to pdf as printer drivers do not support this format
        if self._is_open_office_file(file_to_print):
            logger.info("Converting Office document to pdf")
            folder = os.path.dirname(file_to_print)
            converted_filename = file_to_print + ".pdf"
            converted_path = os.path.join(folder, converted_filename)
            self.safe_check_call(
                command=["unoconv", "-o", converted_path, file_to_print],
                error_status=Status.ERROR_PRINT,
            )
            file_to_print = converted_path

        logger.info("Sending file to printer {}".format(self.printer_name))

        self.safe_check_call(
            command=["xpp", "-P", self.printer_name, file_to_print],
            error_status=Status.ERROR_PRINT,
        )
        # This is an addition to ensure that the entire print job is transferred over.
        # If the job is not fully transferred within the timeout window, the user
        # will see an error message.
        self._wait_for_print()

    def safe_check_call(
        self, command: str, error_status: Status, ignore_stderr_startswith=None
    ):
        """
        Wrap subprocess.check_output to ensure we wrap CalledProcessError and return
        our own exception, and log the error messages.
        """
        try:
            err = subprocess.run(command, check=True, capture_output=True).stderr
            # ppdc and lpadmin may emit warnings we are aware of which should not be treated as
            # user facing errors
            if ignore_stderr_startswith and err.startswith(ignore_stderr_startswith):
                logger.info("Encountered warning: {}".format(err.decode("utf-8")))
            elif err == b"":
                # Nothing on stderr and returncode is 0, we're good
                pass
            else:
                raise ExportException(sdstatus=error_status, sderror=err)
        except subprocess.CalledProcessError as ex:
            raise ExportException(sdstatus=error_status, sderror=ex.output)
