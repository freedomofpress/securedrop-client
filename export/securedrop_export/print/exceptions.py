from securedrop_export.exceptions import ExportException

from .status import Status


class PrinterNotFoundException(ExportException):
    def __init__(self, sderror=None):
        super().__init__()
        self.sdstatus = Status.ERROR_PRINTER_NOT_FOUND
