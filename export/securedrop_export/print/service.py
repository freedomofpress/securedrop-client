import logging
import os
import signal
import subprocess
import time
from pathlib import Path

from securedrop_export.directory import safe_mkdir
from securedrop_export.exceptions import ExportException, TimeoutException, handler

from .status import Status

logger = logging.getLogger(__name__)


# We support viewing, but not printing, these mimetypes.
# In future we should consolidate all our mimetype
# controls into one place.
# See https://github.com/freedomofpress/securedrop-workstation/issues/842,
# https://github.com/freedomofpress/securedrop-workstation/issues/1139
MIMETYPE_UNPRINTABLE = (
    "audio/",
    "video/",
)

# Not unprintable (could print individual files in the archive), just not yet implemented
MIMETYPE_ARCHIVE = [
    "application/vnd.djvu",
    "application/vnd.rar",
    "application/zip",
    "application/x-7z-compressed",
]

# These are a subset of mimetypes that cups supports for direct printing:
# see /usr/share/cups/mime/mime.types
MIMETYPE_PRINT_WITHOUT_CONVERSION = [
    "application/pdf",
    "text/plain",
    "image/gif",
    "image/png",
    "image/jpeg",
    "image/pwg-raster",
    "image/tiff",
    "image/x-photocd",
    "image/x-portable-anymap",
    "image/x-portable-bitmap",
    "image/x-portable-graymap",
    "image/x-portable-pixmap",
    "image/x-sgi-rgb",
    "image/x-xbitmap",
    "image/x-xpixmap",
    "image/x-sun-raster",
    "image/x-bitmap",
    "image/x-icon",
]
LIBREOFFICE_DESKTOP_DIR = Path("/usr/share/applications/")


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
        printer_idle_string = f"printer {self.printer_name} is idle"
        while True:
            try:
                logger.info(f"Running lpstat waiting for printer {self.printer_name}")
                output = subprocess.check_output(["lpstat", "-p", self.printer_name])
                if printer_idle_string in output.decode("utf-8"):
                    logger.info("Print completed")
                    return True
                else:
                    time.sleep(5)
            except subprocess.CalledProcessError:
                raise ExportException(sdstatus=Status.ERROR_PRINT)
            except TimeoutException:
                logger.error(f"Timeout waiting for printer {self.printer_name}")
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
                logger.info(f"{printers} are unsupported printers")
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
                logger.info(f"lpinfo usb printer: {printer_uri}")

        # verify that the printer is supported, else throw
        if printer_uri == "":
            # No usb printer is connected
            logger.info("No usb printers connected")
            raise ExportException(sdstatus=Status.ERROR_PRINTER_NOT_FOUND)
        elif not any(x in printer_uri for x in self.SUPPORTED_PRINTERS):
            # printer url is a make that is unsupported
            logger.info(f"Printer {printer_uri} is unsupported")
            raise ExportException(sdstatus=Status.ERROR_PRINTER_NOT_SUPPORTED)

        logger.info(f"Printer {printer_uri} is supported")
        return printer_uri

    def _install_printer_ppd(self, uri):
        if not any(x in uri for x in self.SUPPORTED_PRINTERS):
            logger.error(f"Cannot install printer ppd for unsupported printer: {uri}")
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
            self.check_output_and_stderr(
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
        logger.info(f"Setting up printer {self.printer_name}")
        self.check_output_and_stderr(
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
        testprint = Path("/usr/share/cups/data/testprint")
        self._print_file(testprint)

    def _print_all_files(self):
        print_directory = Path(Path(self.submission.tmpdir, "export_data"))
        files = os.listdir(print_directory)
        for print_count, f in enumerate(files):
            file_path = Path(print_directory, f)
            self._print_file(file_path)
            logger.info(f"Printing document {print_count + 1} of {len(files)}")

    def _get_supported_mimetypes_libreoffice(self, desktop_dir: Path):
        """
        Return a list of mimetypes supported by Libreoffice programs.

        desktop_dir is a path, such as /usr/share/applications/, specified
        by the constant LIBREOFFICE_DESKTOP_FILES.
        """
        supported_mimetypes: set[str] = set()
        libreoffice_programs = [
            "libreoffice-base",
            "libreoffice-calc",
            "libreoffice-draw",
            "libreoffice-impress",
            "libreoffice-math",
            "libreoffice-writer",
        ]
        for item in libreoffice_programs:
            desktop_file = Path(desktop_dir, f"{item}.desktop")
            if desktop_file.exists():
                with open(desktop_file) as f:
                    for line in f.readlines():
                        if line.startswith("MimeType="):
                            # Semicolon-separated list; don't leave empty element at the end
                            supported_mimetypes.update(line.strip("MimeType=").split(";")[:-1])

        return supported_mimetypes

    def _needs_pdf_conversion(self, filename: Path):
        """
        Checks mimetype of a file and returns True if file must be converted
        to PDF before attempting to print.

        Raises ExportException for unprintable mimetypes or on mimetype
        discovery error.
        """
        mimetype = None
        supported_types: set[str] = set()

        try:
            supported_types = self._get_supported_mimetypes_libreoffice(LIBREOFFICE_DESKTOP_DIR)
        except OSError as e:
            logger.error(f"Could not get supported mimetypes list: {e}")
            raise ExportException(sdstatus=Status.ERROR_MIMETYPE_DISCOVERY)
        if len(supported_types) == 0:
            raise ExportException(sdstatus=Status.ERROR_MIMETYPE_DISCOVERY)

        try:
            # b'filename that may have spaces.docx: application/bla\n'
            # use magic bytes (-M) for filetype detection
            mimetype = (
                subprocess.check_output(["mimetype", filename]).decode().split(":")[-1].strip()
            )
        except subprocess.CalledProcessError:
            logger.error(f"Could not process mimetype of {filename}")
            raise ExportException(sdstatus=Status.ERROR_MIMETYPE_DISCOVERY)
        # Don't print "audio/*", "video/*", or archive mimetypes
        if mimetype.startswith(MIMETYPE_UNPRINTABLE) or mimetype in MIMETYPE_ARCHIVE:
            logger.info(f"Unprintable file {filename}")
            raise ExportException(sdstatus=Status.ERROR_UNPRINTABLE_TYPE)
        elif mimetype in MIMETYPE_PRINT_WITHOUT_CONVERSION:
            # Print directly, no need to convert
            logger.debug(f"{filename} can skip PDF conversion")
            return False
        elif mimetype in supported_types:
            logger.debug(f"{filename} will be converted to PDF")
            return True
        else:
            logger.error("Mimetype is unknown or unsupported.")
            raise ExportException(sdstatus=Status.ERROR_MIMETYPE_UNSUPPORTED)

    def _print_file(self, file_to_print: Path):
        """
        Print a file, attempting to convert to a printable format (PDF)
        if the mimetype is not directly printable.

        file_to_print: Path representing absolute path to target file.
        """
        if self._needs_pdf_conversion(file_to_print):
            logger.info("Convert to pdf for printing")

            # Put converted files in a subdirectory out of an abundance
            # of caution. Libreoffice conversion uses a fixed name and will
            # overwrite existing files of the same name. Right now we
            # only send one file at a time, but if we ever batch these files
            # we don't want to overwrite (eg) memo.pdf with memo.docx
            safe_mkdir(file_to_print.parent, "print-pdf")
            printable_folder = file_to_print.parent / "print-pdf"

            # The filename is deterined by LibreOffice - it's the original stem
            # (name minus extension) plus the new extension (.pdf).
            converted_filename = printable_folder / (file_to_print.stem + ".pdf")
            if converted_filename.exists():
                logger.error("Another file by that name exists already.")
                logger.debug(f"{converted_filename} would be overwritten")
                raise ExportException(sdstatus=Status.ERROR_PRINT)

            args: list[str | Path] = [
                "libreoffice",
                "--headless",
                "--safe-mode",
                "--convert-to",
                "pdf",
                "--outdir",
                printable_folder,
                file_to_print,
            ]

            try:
                logger.debug(f"Convert {file_to_print} to {converted_filename} for printing")
                output = subprocess.check_output(args).decode()
                if "Error" in output:
                    # Even on error, libreoffice returns 0, so we need to check
                    # the output, as well as check that the file exists
                    logger.error("Libreoffice headless conversion error")
                    logger.debug(output)
                    raise ExportException(sdstatus=Status.ERROR_PRINT)

            except subprocess.CalledProcessError as e:
                raise ExportException(sdstatus=Status.ERROR_PRINT, sderror=e.output)

            file_to_print = converted_filename

        if not file_to_print.exists():
            logger.error(f"Something went wrong: {file_to_print} not found")
            raise ExportException(sdstatus=Status.ERROR_PRINT)

        logger.info(f"Sending file to printer {self.printer_name}")
        try:
            # We can switch to using libreoffice --pt $printer_cups_name
            # here, and either print directly (headless) or use the GUI
            subprocess.check_call(
                ["xpp", "-P", self.printer_name, file_to_print],
            )
        except subprocess.CalledProcessError as e:
            raise ExportException(sdstatus=Status.ERROR_PRINT, sderror=e.output)

        # This is an addition to ensure that the entire print job is transferred over.
        # If the job is not fully transferred within the timeout window, the user
        # will see an error message.
        self._wait_for_print()

    def check_output_and_stderr(
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
