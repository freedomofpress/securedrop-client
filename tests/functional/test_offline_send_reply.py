"""
Functional tests for sending messages in the SecureDrop client application. The
tests are based upon the client testing descriptions here:

https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
import pytest
from flaky import flaky
from PyQt5.QtCore import Qt


@flaky
@pytest.mark.vcr()
def test_offline_send_reply_to_source(functional_test_logged_in_context, qtbot, mocker):
    """
    It's NOT possible to send a reply to a source when the client is offline.
    """
    gui, controller, tempdir = functional_test_logged_in_context
    qtbot.wait(1000)

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_widgets.keys()))

    qtbot.waitUntil(check_for_sources, timeout=10000)
    source_ids = list(gui.main_view.source_list.source_widgets.keys())
    first_source_id = source_ids[0]
    first_source_widget = gui.main_view.source_list.source_widgets[first_source_id]
    qtbot.mouseClick(first_source_widget, Qt.LeftButton)

    # Now logout.
    def check_login_button():
        assert gui.left_pane.user_profile.login_button.isVisible()

    gui.left_pane.user_profile.user_button.menu.logout.trigger()
    qtbot.waitUntil(check_login_button, timeout=10000)

    # Check UI won't let user send a reply.
    conversation = gui.main_view.view_layout.itemAt(0).widget()
    text_box = conversation.reply_box.text_edit
    # The text box is disabled.
    assert text_box.isEnabled() is False
    placeholder = text_box.placeholder
    # And the placeholder text is displayed instead.
    assert placeholder.isVisible()
