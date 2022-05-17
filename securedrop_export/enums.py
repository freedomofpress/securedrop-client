from enum import Enum
from typing import TypeVar, Type

T = TypeVar('T', bound=ExportEnum)

class ExportEnum(Enum):
    """
    Parent class for export and print statuses.
    """
    @classmethod
    def value_of(cls: Type[T], target: str) -> T:
        for key, value in cls.__members__.items():
            if key == target:
                return value
        # Don't print the value since we don't know what it is
        raise ValueError("No valid entry found for provided value")


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
