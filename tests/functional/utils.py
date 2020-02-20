"""
Utility functions for setting up and configuring isolated headless functional
tests of the SecureDrop client app's user interface.

The code is copiously commented and you should look at the existing tests for
basic examples of how to configure/write/test. Some of the tests appear to get
into a state that reliably causes subsequent tests a crash. Such tests have
been isolated and are clearly marked. The Makefile is used to ensure we
exercise them in a completely new process.

Use the `qtbot` object to drive the UI. This is a part of the pytest-qt
package whose documentation is here:

https://pytest-qt.readthedocs.io/en/latest/

When writing tests that require the user to log in, on first run of the test
you must make sure the TOTP is correct for the time at which the test is run.
For any further run of the test, this doesn't need to be the case since vcrpy
will replay the original response from the test server. These responses are
stored in the cassettes directory and should be committed to the git
repository. The `vcrpy` module's documentation is here:

https://vcrpy.readthedocs.io/en/latest/

The tests will be run when you `make check` (with everything else) or if you
just `make test-functional`.
"""
import os
import tempfile
import pytest
import subprocess


from PyQt5.QtCore import Qt


from securedrop_client.gui.main import Window
from securedrop_client.logic import Controller
from securedrop_client.gui.widgets import LoginDialog
from securedrop_client.utils import safe_mkdir


HOSTNAME = "http://localhost:8081/"
USERNAME = "journalist"
PASSWORD = "correct horse battery staple profanity oil chewy"


def get_safe_tempdir():
    """
    Return the tempdir to be used to isolate each run of the app in a test.
    """
    return tempfile.TemporaryDirectory()


def get_test_context(sdc_home):
    """
    Returns a tuple containing a Window instance and a Controller instance that
    have been correctly set up and isolated from any other instances of the
    application to be run in the test suite.
    """
    from securedrop_client.db import make_session_maker
    # The application's window.
    gui = Window()
    # Create all app assets in a new temp directory and sub-directories.
    safe_mkdir(os.path.join(sdc_home.name, "gpg"))
    safe_mkdir(os.path.join(sdc_home.name, "data"))
    # Configure test keys.
    create_gpg_test_context(sdc_home)
    # Configure and create the database.
    session_maker = make_session_maker(sdc_home.name)
    create_dev_data(sdc_home.name, session_maker)
    # Create the controller.
    controller = Controller(HOSTNAME, gui, session_maker, sdc_home.name,
                            False, False)
    # Link the gui and controller together.
    gui.controller = controller
    # Et Voila...
    return (gui, controller)


def get_logged_in_test_context(sdc_home, qtbot, totp):
    """
    Returns a tuple containing a Window and Controller instance that have been
    correctly configured to work together, isolated from other runs of the
    test suite and in a logged in state.
    """
    gui, controller = get_test_context(sdc_home)
    gui.setup(controller)
    qtbot.keyClicks(gui.login_dialog.username_field, USERNAME)
    qtbot.keyClicks(gui.login_dialog.password_field, PASSWORD)
    qtbot.keyClicks(gui.login_dialog.tfa_field, totp)
    qtbot.mouseClick(gui.login_dialog.submit, Qt.LeftButton)

    def wait_for_login():
        assert gui.login_dialog is None

    qtbot.waitUntil(wait_for_login, timeout=10000)
    return (gui, controller)


def create_gpg_test_context(sdc_home):
    """
    Ensures the correct key is in the $sdc_home/gpg directory. Needs the
    gpg command to be installed for this to work.
    """
    gpg_home = os.path.join(sdc_home.name, "gpg")
    func_test_path = os.path.dirname(os.path.abspath(__file__))
    key_file = os.path.join(func_test_path, "..", "files",
                            "securedrop.gpg.asc")
    cmd = [
        'gpg',
        '--homedir',
        gpg_home,
        '--allow-secret-key-import',
        '--import',
        os.path.abspath(key_file),
    ]
    result = subprocess.run(cmd)
    if result.returncode != 0:
        raise RuntimeError(
            "Unable to import test GPG key. STDOUT: {} STDERR: {}".format(
                result.stdout, result.stderr
            )
        )


def create_dev_data(sdc_home, session_maker):
    """
    Run the script, "create_dev_data.py". This is used to setup and configure
    the database and GPG keyring related metadata.
    """
    func_test_path = os.path.dirname(os.path.abspath(__file__))
    script_path = os.path.join(func_test_path, "..", "..", "create_dev_data.py")
    cmd = [
        script_path,
        sdc_home,
    ]
    result = subprocess.run(cmd)
    if result.returncode != 0:
        raise RuntimeError(
            "Unable to configure database. STDOUT: {} STDERR: {}".format(
                result.stdout, result.stderr
            )
        )


def test_login_ensure_errors_displayed(qtbot, mocker):
    """
    We see an error if incomplete credentials are supplied to the login dialog.
    """
    w = Window()
    login_dialog = LoginDialog(w)
    login_dialog.show()
    assert login_dialog.error_bar.error_status_bar.text() == ""
    qtbot.keyClicks(login_dialog.username_field, "journalist")
    qtbot.mouseClick(login_dialog.submit, Qt.LeftButton)
    expected = "Please enter a username, password and two-factor code."
    actual = login_dialog.error_bar.error_status_bar.text()
    assert actual == expected


@pytest.mark.vcr()  # Ensure any API network traffic is recorded/replayed.
def test_login_as_journalist(qtbot, mocker):
    """
    The app is visible if the user logs in with apparently correct credentials.
    """
    # Once out of scope, is deleted.
    tempdir = get_safe_tempdir()
    # Create a clean context.
    gui, controller = get_test_context(tempdir)
    gui.setup(controller)
    # Fill in UI with good credentials.
    qtbot.keyClicks(gui.login_dialog.username_field, USERNAME)
    qtbot.keyClicks(gui.login_dialog.password_field, PASSWORD)
    qtbot.keyClicks(gui.login_dialog.tfa_field, "493941")
    # The waitSignal context handler is used to allow the API thread to call
    # and then (ultimately) emit the expected signal. This pattern will need to
    # be used with some API calls. For more information about this method, see:
    # https://pytest-qt.readthedocs.io/en/latest/signals.html
    with qtbot.waitSignal(controller.authentication_state, timeout=10000):
        qtbot.mouseClick(gui.login_dialog.submit, Qt.LeftButton)
    # The main window is visible (indicating a successful login).
    assert gui.isVisible()
    # The login box no longer exists.
    assert gui.login_dialog is None


@pytest.mark.vcr()
def test_send_reply_to_source(qtbot, mocker):
    """
    It's possible to send a reply to a source and see it show up in the
    conversation window.
    """
    totp = "778326"
    tempdir = get_safe_tempdir()
    gui, controller = get_logged_in_test_context(tempdir, qtbot, totp)
    qtbot.wait(1000)

    def check_for_sources():
        assert len(list(gui.main_view.source_list.source_widgets.keys()))

    qtbot.waitUntil(check_for_sources, timeout=10000)
    source_ids = list(gui.main_view.source_list.source_widgets.keys())
    first_source_id = source_ids[0]
    first_source_widget = gui.main_view.source_list.source_widgets[first_source_id]
    qtbot.mouseClick(first_source_widget, Qt.LeftButton)
    # Type something into the reply box and click the send button.
    message = "Hello, world!"
    conversation = gui.main_view.view_layout.itemAt(0).widget()
    # Focus on reply box text entry.
    qtbot.mouseClick(conversation.reply_box.text_edit, Qt.LeftButton)
    # Type in a message to the reply box.
    qtbot.keyClicks(conversation.reply_box.text_edit, message)
    qtbot.wait(1000)
    # Wait until the result of the click on the send button has caused the
    # reply_sent signal to trigger.
    with qtbot.waitSignal(conversation.reply_box.reply_sent):
        qtbot.mouseClick(conversation.reply_box.send_button, Qt.LeftButton)
    qtbot.wait(1000)
    # Ensure the last widget in the conversation view contains the text we
    # just typed.
    last_msg_id = list(conversation.conversation_view.current_messages.keys())[-1]
    last_msg = conversation.conversation_view.current_messages[last_msg_id]
    assert last_msg.message.text() == message
