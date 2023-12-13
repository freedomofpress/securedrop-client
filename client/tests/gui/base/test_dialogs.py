import pytest
from PyQt5.QtCore import QEvent, Qt
from PyQt5.QtGui import QKeyEvent
from PyQt5.QtWidgets import QMainWindow

from securedrop_client.gui.base import ModalDialog
from tests.helper import app  # noqa: F401


@pytest.fixture(scope="function")
def modal_dialog(mocker, homedir):
    mocker.patch("PyQt5.QtWidgets.QApplication.activeWindow", return_value=QMainWindow())

    dialog = ModalDialog()

    yield dialog


@pytest.mark.parametrize("key", [Qt.Key_Enter, Qt.Key_Return])
def test_ModalDialog_keyPressEvent_does_not_close_on_enter_or_return(mocker, modal_dialog, key):
    modal_dialog.close = mocker.MagicMock()

    event = QKeyEvent(QEvent.KeyPress, key, Qt.NoModifier)
    modal_dialog.keyPressEvent(event)

    modal_dialog.close.assert_not_called()


@pytest.mark.parametrize("key", [Qt.Key_Enter, Qt.Key_Return])
def test_ModalDialog_keyPressEvent_cancel_on_enter_when_focused(mocker, modal_dialog, key):
    modal_dialog.cancel_button.click = mocker.MagicMock()
    modal_dialog.cancel_button.hasFocus = mocker.MagicMock(return_value=True)

    event = QKeyEvent(QEvent.KeyPress, key, Qt.NoModifier)
    modal_dialog.keyPressEvent(event)

    modal_dialog.cancel_button.click.assert_called_once_with()


@pytest.mark.parametrize("key", [Qt.Key_Enter, Qt.Key_Return])
def test_ModalDialog_keyPressEvent_continue_on_enter(mocker, modal_dialog, key):
    modal_dialog.continue_button.click = mocker.MagicMock()

    event = QKeyEvent(QEvent.KeyPress, key, Qt.NoModifier)
    modal_dialog.keyPressEvent(event)

    modal_dialog.continue_button.click.assert_called_once_with()


@pytest.mark.parametrize("key", [Qt.Key_Alt, Qt.Key_A])
def test_ModalDialog_keyPressEvent_does_not_close_for_other_keys(mocker, modal_dialog, key):
    modal_dialog.close = mocker.MagicMock()

    event = QKeyEvent(QEvent.KeyPress, key, Qt.NoModifier)
    modal_dialog.keyPressEvent(event)

    modal_dialog.close.assert_not_called()


def test_ModalDialog_animation_of_activestate(mocker, modal_dialog):
    assert modal_dialog.button_animation
    modal_dialog.button_animation.start = mocker.MagicMock()
    modal_dialog.button_animation.stop = mocker.MagicMock()
    modal_dialog.continue_button = mocker.MagicMock()

    # Check the animation frame is updated as expected.
    modal_dialog.animate_activestate()
    assert modal_dialog.continue_button.setIcon.call_count == 1
    modal_dialog.continue_button.reset_mock()

    # Check starting the animated state works as expected.
    modal_dialog.start_animate_activestate()
    modal_dialog.button_animation.start.assert_called_once_with()
    modal_dialog.continue_button.setText.assert_called_once_with("")
    assert modal_dialog.continue_button.setMinimumSize.call_count == 1
    assert modal_dialog.continue_button.setStyleSheet.call_count == 2  # also called once for reset

    modal_dialog.continue_button.reset_mock()

    # Check stopping the animated state works as expected.
    modal_dialog.stop_animate_activestate()
    modal_dialog.button_animation.stop.assert_called_once_with()
    modal_dialog.continue_button.setText.assert_called_once_with("CONTINUE")
    assert modal_dialog.continue_button.setIcon.call_count == 1
    assert modal_dialog.continue_button.setStyleSheet.call_count == 2  # also called once for reset


def test_ModalDialog_animation_of_header(mocker, modal_dialog):
    assert modal_dialog.header_animation
    modal_dialog.header_animation.start = mocker.MagicMock()
    modal_dialog.header_animation.stop = mocker.MagicMock()
    modal_dialog.header_icon.setVisible = mocker.MagicMock()
    modal_dialog.header_spinner_label.setVisible = mocker.MagicMock()
    modal_dialog.header_spinner_label.setPixmap = mocker.MagicMock()

    # Check the animation frame is updated as expected.
    modal_dialog.animate_header()
    assert modal_dialog.header_spinner_label.setPixmap.call_count == 1

    # Check starting the animated state works as expected.
    modal_dialog.start_animate_header()
    modal_dialog.header_animation.start.assert_called_once_with()
    modal_dialog.header_icon.setVisible.assert_called_once_with(False)
    modal_dialog.header_spinner_label.setVisible.assert_called_once_with(True)

    modal_dialog.header_icon.setVisible.reset_mock()
    modal_dialog.header_spinner_label.setVisible.reset_mock()

    # Check stopping the animated state works as expected.
    modal_dialog.stop_animate_header()
    modal_dialog.header_animation.stop.assert_called_once_with()
    modal_dialog.header_icon.setVisible.assert_called_once_with(True)
    modal_dialog.header_spinner_label.setVisible.assert_called_once_with(False)
