from enum import Enum

class ExportEnum(Enum):
    """
    Parent class for export and print statuses.
    """

class Command(ExportEnum):
    """
    All supported commands.

    Values are as supplied by the calling VM (sd-app), and a change in any values require
    corresponding changes in the calling VM.
    """
    PRINTER_PREFLIGHT = "printer-preflight"
    PRINTER_TEST = "printer-test"
    PRINT = "printer"
    CHECK_USBS = "usb-test"
    CHECK_VOLUME = "disk-test"
    EXPORT = "disk"
    START_VM = ""

    @classmethod
    def printer_actions(cls):
        return (cls.PRINTER_PREFLIGHT, cls.PRINTER_TEST, cls.PRINT)

    @classmethod
    def export_actions(cls):
        return (cls.EXPORT, cls.CHECK_USBS, cls.CHECK_VOLUME)
