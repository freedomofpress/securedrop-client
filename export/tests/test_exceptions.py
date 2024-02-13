import signal

import pytest

from securedrop_export.exceptions import TimeoutException, handler


def test_handler():
    signal.signal(signal.SIGALRM, handler)
    signal.setitimer(signal.ITIMER_REAL, 0.001)

    with pytest.raises(TimeoutException):
        _run_handler_routine()


def _run_handler_routine():
    try:
        while True:
            continue
    except TimeoutException:
        raise
