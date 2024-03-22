from PyQt5.QtGui import QPalette


def test_styles(modal_dialog):
    error_details = modal_dialog.error_details

    assert error_details.getContentsMargins() == (36, 0, 40, 0)
    assert error_details.palette().color(QPalette.Foreground).name() == "#ff0064"
    assert error_details.font().family() == "Montserrat"
    assert error_details.font().pixelSize() == 16

    modal_dialog.start_animate_activestate()

    assert error_details.getContentsMargins() == (36, 0, 40, 0)
    assert error_details.palette().color(QPalette.Foreground).name() == "#ff66c4"
    assert error_details.font().family() == "Montserrat"
    assert error_details.font().pixelSize() == 16
