import time

from PyQt5.QtCore import QTimer
from PyQt5.QtWidgets import QApplication

app = QApplication([])


DEFAULT_WAIT_TIMEOUT = 5000
ACTION_DELAY = 100  # << DEFAULT_WAIT_TIMEOUT

FLAKY_MAX_RUNS = 10
FLAKY_MIN_PASSES = 9


def assertEmissions(testcase, signal_emissions, count, timeout=5000) -> bool:
    if len(signal_emissions) < count:
        signal_emissions.wait(timeout)

    testcase.assertEqual(len(signal_emissions), count)


def emitsSignals(act):
    """Delays the action just enough for wait statements to be executed."""
    QTimer.singleShot(100, act)


def tearDownQtObjects():
    """Introduces a short delay to give time to Qt objects to be torn down."""
    time.sleep(0.1)  # Really. Prevents segfaults... :'(
