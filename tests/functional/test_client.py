import os
import tempfile
import json
import pytest


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
OTP = "783682"


def get_safe_tempdir():
    return tempfile.TemporaryDirectory()


def get_test_context(sdc_home, mocker):
    """
    Returns a tuple containing a Window instance and a Controller instance that
    have been correctly set up and isolated from any other instances of the
    application to be run in the test suite.
    """
    gui = Window()  # The application's wind
    # Create all app assets in a new temp directory and sub-directories.
    safe_mkdir(os.path.join(sdc_home.name, "gpg"))
    safe_mkdir(os.path.join(sdc_home.name, "data"))
    # Configure and create the database.
    session_maker = make_session_maker(sdc_home.name)
    create_dev_data(sdc_home.name, session_maker)
    # Create the controller.
    controller = Controller(HOSTNAME, gui, session_maker, sdc_home.name,
                            False, False)
    # Link the gui and controller together.
    gui.controller = controller
    # Et Voila...
    with mocker.patch("securedrop_client.logic.sdclientapi") as mock_api:
        return (gui, controller, mock_api)


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


def test_login_as_journalist(qtbot, mocker):
    """
    The app is visible if the user logs in with apparently correct credentials.
    """
    tempdir = get_safe_tempdir()  # Once out of scope, is deleted.
    gui, controller, mock_api = get_test_context(tempdir, mocker)
    login_dialog = LoginDialog(gui)
    login_dialog.setup(controller)
    gui.login_dialog = login_dialog
    login_dialog.show()
    assert login_dialog.error_bar.error_status_bar.text() == ""
    qtbot.keyClicks(login_dialog.username_field, USERNAME)
    qtbot.keyClicks(login_dialog.password_field, PASSWORD)
    qtbot.keyClicks(login_dialog.tfa_field, OTP)
    qtbot.mouseClick(login_dialog.submit, Qt.LeftButton)
    assert gui.isVisible() 
