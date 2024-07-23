from PyQt5.QtTest import QSignalSpy

from securedrop_client.gui.base.checkbox import SDCheckBox
from tests.helper import app  # noqa: F401


def test_SDCheckBox():
    checkbox_area = SDCheckBox()
    signal_emissions = QSignalSpy(checkbox_area.clicked)

    checkbox_area.mousePressEvent(None)

    assert len(signal_emissions) == 1
