from PyQt5.QtGui import QPalette


def test_styles(modal_dialog):
    continue_button = modal_dialog.continue_button

    assert continue_button.palette().color(QPalette.Foreground).name() == "#ffffff"
    assert continue_button.palette().color(QPalette.Background).name() == "#2a319d"

    continue_button.setEnabled(False)

    assert continue_button.palette().color(QPalette.Foreground).name() == "#e1e2f1"
    assert continue_button.palette().color(QPalette.Background).name() == "#c2c4e3"

    modal_dialog.start_animate_activestate()

    assert continue_button.palette().color(QPalette.Foreground).name() == "#ffffff"
    assert continue_button.palette().color(QPalette.Background).name() == "#f1f1f6"
