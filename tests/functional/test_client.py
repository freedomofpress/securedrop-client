"""
Functional tests for the SecureDrop client application. The tests are based
upon the client testing descriptions here:

https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing

The code is copiously commented and you should look at test_login_as_journalist
for a basic example of how to configure/write/test.

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
import json
import pytest
import subprocess


from sqlalchemy.orm.exc import NoResultFound


from PyQt5.QtCore import Qt


from securedrop_client.gui.main import Window
from securedrop_client.logic import Controller
from securedrop_client.config import Config
from securedrop_client.gui.widgets import LoginDialog
from securedrop_client.db import Base, make_session_maker, ReplySendStatus, ReplySendStatusCodes
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
    with qtbot.waitSignal(controller.authentication_state, timeout=10000):
        qtbot.mouseClick(gui.login_dialog.submit, Qt.LeftButton)
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
    subprocess.call(cmd)


def create_dev_data(sdc_home, session_maker):
    """
    Based upon the functionality in the script, create_dev_data.py. This is
    used to setup and configure the database and GPG keyring related metadata.
    """
    session = session_maker()
    Base.metadata.create_all(bind=session.get_bind())
    with open(os.path.join(sdc_home, Config.CONFIG_NAME), 'w') as f:
        f.write(json.dumps({
            'journalist_key_fingerprint': '65A1B5FF195B56353CC63DFFCC40EF1228271441',
        }))
    for reply_send_status in ReplySendStatusCodes:
        try:
            reply_status = session.query(ReplySendStatus).filter_by(
                    name=reply_send_status.value).one()
        except NoResultFound:
            reply_status = ReplySendStatus(reply_send_status.value)
            session.add(reply_status)
            session.commit()


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
    # be used with all API calls. For more information about this method, see:
    # https://pytest-qt.readthedocs.io/en/latest/signals.html
    with qtbot.waitSignal(controller.authentication_state, timeout=10000):
        qtbot.mouseClick(gui.login_dialog.submit, Qt.LeftButton)
    # The main window is visible (indicating a successful login).
    assert gui.isVisible()
    # The login box no longer exists.
    assert gui.login_dialog is None


@pytest.mark.vcr()
def test_logout_as_journalist(qtbot, mocker):
    """
    A journalist can successfully log out of the application.
    """
    totp = "670099"
    tempdir = get_safe_tempdir()
    gui, controller = get_logged_in_test_context(tempdir, qtbot, totp)
    qtbot.wait(100)
    with qtbot.waitSignal(controller.authentication_state, timeout=10000):
        # The qtbot object cannot interact with QAction items (as used in the
        # logout button/menu), so we're forced to programatically trigger it
        # rather than pretend some sort of user interaction via the qtbot.
        gui.left_pane.user_profile.user_button.menu.logout.trigger()
    # The login button is visible - demonstrating the user is logged out.
    assert gui.left_pane.user_profile.login_button.isVisible()
