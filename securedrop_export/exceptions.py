import logging

from typing import Optional

from .enums import ExportEnum

logger = logging.getLogger(__name__)


class ExportException(Exception):
    """
    Base class for exceptions encountered during export.
    """

    def __init__(self, *args, **kwargs):
        super().__init__(*args)
        self._status = kwargs.get("status")

    @property
    def status(self) -> Optional[ExportEnum]:
        try:
            return ExportEnum.value_of(self._status)
        except ValueError:
            logger.error(
                "Unexpected value passed to ExportException (ExportEnum is required)."
            )
            pass  # Don't return a status


class TimeoutException(ExportException):
    pass


def handler(signum, frame):
    """
    This is a signal handler used for raising timeouts:
    https://docs.python.org/3/library/signal.html#signal.signal
    """
    raise TimeoutException("Timeout")
