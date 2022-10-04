from enum import Enum

class Command(Enum):
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
