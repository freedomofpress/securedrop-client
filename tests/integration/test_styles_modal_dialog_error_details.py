from PyQt5.QtGui import QPalette


def test_styles_for_modal_dialog(modal_dialog):
    error_details = modal_dialog.error_details
    # assert margin: 0px 40px 0px 36px;
    assert '#ff0064' == error_details.palette().color(QPalette.Foreground).name()
    assert 'Montserrat' == error_details.font().family()
    assert 16 == error_details.font().pixelSize()
    modal_dialog.start_animate_activestate()
    # assert margin: 0px 40px 0px 36px;
    assert '#ff66c4' == error_details.palette().color(QPalette.Foreground).name()
    assert 'Montserrat' == error_details.font().family()
    assert 16 == error_details.font().pixelSize()
