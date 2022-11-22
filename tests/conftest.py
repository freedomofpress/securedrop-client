import json
import os
import subprocess
import tempfile
from configparser import ConfigParser
from datetime import datetime
from uuid import uuid4

import pytest
from PyQt5.QtCore import Qt
from PyQt5.QtWidgets import QMainWindow

from securedrop_client import export, state
from securedrop_client.app import configure_locale_and_language
from securedrop_client.config import Config
from securedrop_client.db import (
    Base,
    DownloadError,
    DownloadErrorCodes,
    ReplySendStatus,
    ReplySendStatusCodes,
    Source,
    make_session_maker,
)
from securedrop_client.gui import conversation
from securedrop_client.gui.main import Window
from securedrop_client.logic import Controller

with open(os.path.join(os.path.dirname(__file__), "files", "test-key.gpg.pub.asc")) as f:
    PUB_KEY = f.read()


HOSTNAME = "http://localhost:8081/"
USERNAME = "journalist"
PASSWORD = "correct horse battery staple profanity oil chewy"

# Modify cassettes to use the following TOTP code. For developing new tests,
# you can modify this so you don't need to keep editing cassettes during
# development.
TOTP = "123456"

# Time (in milliseconds) to wait for these GUI elements to render.
TIME_APP_START = 1000
TIME_LOGIN = 10000
TIME_LOGOUT = 10000
TIME_SYNC = 10000
TIME_CLICK_ACTION = 1000
TIME_RENDER_SOURCE_LIST = 20000
TIME_RENDER_CONV_VIEW = 1000
TIME_RENDER_EXPORT_DIALOG = 1000
TIME_FILE_DOWNLOAD = 5000


@pytest.fixture(scope="function")
def lang(request):
    """
    Setup:  Override $LANG as parameterized and configure locale accordingly.

    Teardown:  Restore original $LANG and locale configuration.

    Must be used with "indirect" to wrap setup and teardown at runtime.
    """
    lang = request.param

    LANG = os.environ.get("LANG", "")
    os.environ["LANG"] = lang
    configure_locale_and_language()

    yield lang

    os.environ["LANG"] = LANG
    configure_locale_and_language()


@pytest.fixture(scope="function")
def print_dialog(mocker, homedir):
    mocker.patch("PyQt5.QtWidgets.QApplication.activeWindow", return_value=QMainWindow())

    export_device = mocker.MagicMock(spec=conversation.ExportDevice)

    dialog = conversation.PrintFileDialog(export_device, "file_UUID", "file123.jpg")

    yield dialog


@pytest.fixture(scope="function")
def export_dialog(mocker, homedir):
    mocker.patch("PyQt5.QtWidgets.QApplication.activeWindow", return_value=QMainWindow())

    export_device = mocker.MagicMock(spec=conversation.ExportDevice)

    dialog = conversation.ExportFileDialog(export_device, "file_UUID", "file123.jpg")

    yield dialog


@pytest.fixture(scope="function")
def i18n():
    """
    Set up locale/language/gettext functions. This enables the use of _().
    """
    configure_locale_and_language()


@pytest.fixture(scope="function")
def homedir(i18n):
    """
    Create a "homedir" for a client.

    Using `mkdtemp` and not `TemporaryDirectory` because the latter will remove the directory
    when the object is destroyed, and we want to leave it on the file system so developers can
    inspect the contents for debugging purposes.
    """

    tmpdir = tempfile.mkdtemp(prefix="sdc-")
    os.chmod(tmpdir, 0o0700)

    data_dir = os.path.join(tmpdir, "data")
    gpg_dir = os.path.join(tmpdir, "gpg")
    logs_dir = os.path.join(tmpdir, "logs")

    for dir_ in [data_dir, gpg_dir, logs_dir]:
        os.mkdir(dir_)
        os.chmod(dir_, 0o0700)

    yield tmpdir


@pytest.fixture(scope="function")
def export_service():
    """An export service that assumes the Qubes RPC calls are successful and skips them."""
    export_service = export.Service()
    # Ensure the export_service doesn't rely on Qubes OS:
    export_service._run_disk_test = lambda dir: None
    export_service._run_usb_test = lambda dir: None
    export_service._run_disk_export = lambda dir, paths, passphrase: None
    export_service._run_printer_preflight = lambda dir: None
    export_service._run_print = lambda dir, paths: None
    return export_service


@pytest.fixture(scope="function")
def functional_test_app_started_context(
    homedir, reply_status_codes, session, config, qtbot, export_service
):
    """
    Returns a tuple containing the gui window and controller of a configured client. This should be
    used to for tests that need to start from the login dialog before the main application window
    is visible.
    """
    app_state = state.State()
    gui = Window(app_state, export_service)
    create_gpg_test_context(homedir)  # Configure test keys
    session_maker = make_session_maker(homedir)  # Configure and create the database
    controller = Controller(HOSTNAME, gui, session_maker, homedir, app_state, False, False)
    gui.setup(controller)  # Connect the gui to the controller

    def login_dialog_is_visible():
        assert gui.login_dialog is not None

    qtbot.waitUntil(login_dialog_is_visible, timeout=TIME_APP_START)

    return (gui, controller)


@pytest.fixture(scope="function")
def functional_test_logged_in_context(functional_test_app_started_context, qtbot):
    """
    Returns a tuple containing the gui window and controller of a configured client after logging in
    with our test user account.
    """
    gui, controller = functional_test_app_started_context

    # Authenticate our test account and login in
    qtbot.keyClicks(gui.login_dialog.username_field, USERNAME)
    qtbot.wait(TIME_CLICK_ACTION)
    qtbot.keyClicks(gui.login_dialog.password_field, PASSWORD)
    qtbot.keyClicks(gui.login_dialog.tfa_field, TOTP)
    qtbot.mouseClick(gui.login_dialog.submit, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)

    def logged_in():
        assert gui.login_dialog is None
        assert gui.isVisible()

    qtbot.waitUntil(logged_in, timeout=TIME_LOGIN)

    return (gui, controller)


@pytest.fixture(scope="function")
def functional_test_offline_context(functional_test_logged_in_context, qtbot):
    """
    Returns a tuple containing the gui window and controller of a configured client after making
    sure we have sources from a sync before switching to offline mode.
    """
    gui, controller = functional_test_logged_in_context

    # The controller begins a sync as soon as the user authentication is successful so we just
    # need to wait for the length of a sync to ensure the local db is up to date with the server
    qtbot.wait(TIME_SYNC)

    # Trigger log out
    # Note: The qtbot object cannot interact with QAction items (as used in the logout button/menu),
    # so we programatically logout rather than using the GUI via qtbot
    gui.left_pane.user_profile.user_button.menu.logout.trigger()

    def check_login_button():
        assert gui.left_pane.user_profile.login_button.isVisible()

    # When the login button appears then we know we're now in offline mode
    qtbot.waitUntil(check_login_button, timeout=TIME_LOGOUT)

    return (gui, controller)


@pytest.fixture(scope="function")
def config(homedir) -> str:
    full_path = os.path.join(homedir, Config.CONFIG_NAME)
    with open(full_path, "w") as f:
        f.write(
            json.dumps({"journalist_key_fingerprint": "65A1B5FF195B56353CC63DFFCC40EF1228271441"})
        )
    return full_path


@pytest.fixture(scope="function")
def alembic_config(homedir):
    return _alembic_config(homedir)


def _alembic_config(homedir):
    base_dir = os.path.join(os.path.dirname(__file__), "..")
    migrations_dir = os.path.join(base_dir, "alembic")
    ini = ConfigParser()
    ini.read(os.path.join(base_dir, "alembic.ini"))

    ini.set("alembic", "script_location", os.path.join(migrations_dir))
    ini.set("alembic", "sqlalchemy.url", "sqlite:///{}".format(os.path.join(homedir, "svs.sqlite")))

    alembic_path = os.path.join(homedir, "alembic.ini")

    with open(alembic_path, "w") as f:
        ini.write(f)

    return alembic_path


@pytest.fixture(scope="function")
def session_maker(homedir):
    return make_session_maker(homedir)


@pytest.fixture(scope="function")
def session(session_maker):
    sess = session_maker
    Base.metadata.create_all(bind=sess.get_bind(), checkfirst=False)
    yield sess
    sess.close()


@pytest.fixture(scope="function")
def reply_status_codes(session) -> None:
    for reply_send_status in ReplySendStatusCodes:
        reply_status = ReplySendStatus(reply_send_status.value)
        session.add(reply_status)
        session.commit()
    return


@pytest.fixture(scope="function")
def download_error_codes(session) -> None:
    for download_error_code in DownloadErrorCodes:
        download_error = DownloadError(download_error_code.name)
        session.add(download_error)
        session.commit()
    return


@pytest.fixture(scope="function")
def source(session) -> dict:
    args = {"uuid": str(uuid4()), "public_key": PUB_KEY}
    source = Source(
        journalist_designation="foo-bar",
        is_flagged=False,
        interaction_count=0,
        is_starred=False,
        last_updated=datetime.now(),
        document_count=0,
        **args
    )
    args["fingerprint"] = source.fingerprint = "B2FF7FB28EED8CABEBC5FB6C6179D97BCFA52E5F"
    session.add(source)
    session.commit()
    args["id"] = source.id
    args["source"] = source
    return args


def create_gpg_test_context(sdc_home):
    """
    Ensures the correct key is in the $sdc_home/gpg directory. Needs the
    gpg command to be installed for this to work.
    """
    gpg_home = os.path.join(sdc_home, "gpg")
    func_test_path = os.path.dirname(os.path.abspath(__file__))
    key_file = os.path.join(func_test_path, "files", "securedrop.gpg.asc")
    cmd = [
        "gpg",
        "--homedir",
        gpg_home,
        "--allow-secret-key-import",
        "--import",
        os.path.abspath(key_file),
    ]
    result = subprocess.run(cmd)
    if result.returncode != 0:
        raise RuntimeError(
            "Unable to import test GPG key. STDOUT: {} STDERR: {}".format(
                result.stdout, result.stderr
            )
        )
