"""
Functional tests for sending messages in the SecureDrop client application. The
tests are based upon the client testing descriptions here:

https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import os
import pytest
from flaky import flaky
from PyQt5.QtCore import Qt
import pyautogui

from tests.conftest import (TIME_APP_START, TIME_RENDER_CONV_VIEW,
                            TIME_RENDER_SOURCE_LIST)
IMG_DIR = os.path.join(os.path.dirname(__file__), "testimages")


@flaky
@pytest.mark.vcr()
def test_offline_nostar_for_hover(functional_test_logged_in_context, qtbot):
    """
    It's NOT possible to star a source when the client is offline.
    """

    gui, controller, homedir = functional_test_logged_in_context
    qtbot.wait(TIME_APP_START)

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_widgets.keys()))

    qtbot.waitUntil(check_for_sources, timeout=TIME_RENDER_SOURCE_LIST)
    source_ids = list(gui.main_view.source_list.source_widgets.keys())
    first_source_id = source_ids[0]
    first_source_widget = gui.main_view.source_list.source_widgets[first_source_id]

    second_source_id = source_ids[1]
    second_source_widget = gui.main_view.source_list.source_widgets[second_source_id]

    qtbot.mouseClick(first_source_widget, Qt.LeftButton)

    # Now logout.
    def check_login_button():
        assert gui.left_pane.user_profile.login_button.isVisible()

    gui.left_pane.user_profile.user_button.menu.logout.trigger()
    qtbot.waitUntil(check_login_button, timeout=TIME_RENDER_CONV_VIEW)

    # Check the source isn't checked.
    assert first_source_widget.star.isChecked() is False
    # Click it.
    star_path = os.path.join(IMG_DIR, "star.png")
    star_location = pyautogui.locateCenterOnScreen(star_path, confidence=0.8)

    # take the mouse pointer there with 0.5 seconds time
    pyautogui.moveTo(star_location.x, star_location.y, 0.5)

    # Check the source isn't checked.
    assert first_source_widget.star.isChecked() is False
    assert second_source_widget.star.isChecked() is False

    bigdatewidget_path = os.path.join(IMG_DIR, "big_date_25feb.png")
    bigdatewidget_location = pyautogui.locateCenterOnScreen(bigdatewidget_path, confidence=0.8)

    # take the mouse pointer
    pyautogui.moveTo(bigdatewidget_location.x, bigdatewidget_location.y)

    # Check the source isn't checked.
    assert first_source_widget.star.isChecked() is False
    assert second_source_widget.star.isChecked() is False
