from PyQt5.QtGui import QPalette


def test_styles(modal_dialog):
    error_details = modal_dialog.error_details

    assert (36, 0, 40, 0) == error_details.getContentsMargins()
    assert "#ff0064" == error_details.palette().color(QPalette.Foreground).name()
    assert "Montserrat" == error_details.font().family()
    assert 16 == error_details.font().pixelSize()

    modal_dialog.start_animate_activestate()

    assert (36, 0, 40, 0) == error_details.getContentsMargins()
    assert "#ff66c4" == error_details.palette().color(QPalette.Foreground).name()
    assert "Montserrat" == error_details.font().family()
    assert 16 == error_details.font().pixelSize()
