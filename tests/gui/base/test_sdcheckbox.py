from PyQt5.QtTest import QSignalSpy
from PyQt5.QtWidgets import QApplication

from securedrop_client.gui.base.checkbox import SDCheckBox

app = QApplication([])


def test_SDCheckBox():
    checkbox_area = SDCheckBox()
    signal_emissions = QSignalSpy(checkbox_area.clicked)

    checkbox_area.mousePressEvent(None)

    assert len(signal_emissions) == 1
