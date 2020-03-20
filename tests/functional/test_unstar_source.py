"""
Functional tests for sending messages in the SecureDrop client application. The
tests are based upon the client testing descriptions here:

https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
from PyQt5.QtCore import Qt
from .utils import get_safe_tempdir, get_logged_in_test_context


@pytest.mark.vcr()
def test_unstar_source(qtbot, mocker):
    """
    It's possible to un-star a source and see its updated status.
    """
    totp = "270661"
    tempdir = get_safe_tempdir()
    gui, controller = get_logged_in_test_context(tempdir, qtbot, totp)
    qtbot.wait(1000)

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_widgets.keys()))

    qtbot.waitUntil(check_for_sources, timeout=10000)
    source_ids = list(gui.main_view.source_list.source_widgets.keys())
    first_source_id = source_ids[1]
    first_source_widget = gui.main_view.source_list.source_widgets[first_source_id]
    qtbot.mouseClick(first_source_widget, Qt.LeftButton)

    # Check the source IS checked.
    assert first_source_widget.star.isChecked() is True
    # Click it again to toggle it off.
    qtbot.mouseClick(first_source_widget.star, Qt.LeftButton)
    qtbot.wait(1000)
    # Check the source isn't checked once more.
    assert first_source_widget.star.is_starred is False
