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
