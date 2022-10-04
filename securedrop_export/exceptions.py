import logging
from typing import Optional

logger = logging.getLogger(__name__)


class ExportException(Exception):
    """
    Base class for exceptions encountered during export.
    In order to make use of additional attributes `sdstatus` and `sderror`,
    pass them as keyword arguments when raising ExportException.
    """

    def __init__(self, *args, **kwargs):
        super().__init__(*args)
        self.sdstatus = kwargs.get("sdstatus")
        self.sderror = kwargs.get("sderror")

class TimeoutException(ExportException):
    pass


def handler(signum, frame):
    """
    This is a signal handler used for raising timeouts:
    https://docs.python.org/3/library/signal.html#signal.signal
    """
    raise TimeoutException("Timeout")
