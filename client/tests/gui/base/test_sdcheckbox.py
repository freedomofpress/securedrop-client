from PyQt5.QtTest import QSignalSpy

from securedrop_client.gui.base.checkbox import SDCheckBox


def test_SDCheckBox():
    checkbox_area = SDCheckBox()
    signal_emissions = QSignalSpy(checkbox_area.clicked)

    checkbox_area.mousePressEvent(None)

    assert len(signal_emissions) == 1
