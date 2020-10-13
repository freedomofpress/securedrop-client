from PyQt5.QtGui import QPalette


def test_styles(modal_dialog):
    continue_button = modal_dialog.continue_button

    assert "#ffffff" == continue_button.palette().color(QPalette.Foreground).name()
    assert "#2a319d" == continue_button.palette().color(QPalette.Background).name()

    continue_button.setEnabled(False)

    assert "#e1e2f1" == continue_button.palette().color(QPalette.Foreground).name()
    assert "#c2c4e3" == continue_button.palette().color(QPalette.Background).name()

    modal_dialog.start_animate_activestate()

    assert "#ffffff" == continue_button.palette().color(QPalette.Foreground).name()
    assert "#f1f1f6" == continue_button.palette().color(QPalette.Background).name()
