from PyQt5.QtWidgets import QApplication

from securedrop_client.gui.base.checkbox import SDCheckBox

app = QApplication([])


def test_SDCheckBox(mocker):
    checkbox_area = SDCheckBox()
    checkbox_area.clicked = mocker.MagicMock()
    checkbox_area.mousePressEvent(None)
    checkbox_area.clicked.emit.assert_called_once_with()
