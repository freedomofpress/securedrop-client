import os
import subprocess
import tempfile
from configparser import ConfigParser
from datetime import datetime
from unittest import mock
from uuid import uuid4

import pyotp
import pytest
import vcr
from PyQt5.QtCore import Qt
from PyQt5.QtWidgets import QMainWindow

from securedrop_client import state
from securedrop_client.app import configure_locale_and_language
from securedrop_client.db import (
    Base,
    DownloadError,
    DownloadErrorCodes,
    ReplySendStatus,
    ReplySendStatusCodes,
    Source,
    make_session_maker,
)
from securedrop_client.export import Export
from securedrop_client.export_status import ExportStatus
from securedrop_client.gui import conversation
from securedrop_client.gui.main import Window
from securedrop_client.logic import Controller
from tests.sdk.utils import VCRAPI, Cassette

with open(os.path.join(os.path.dirname(__file__), "files", "test-key.gpg.pub.asc")) as f:
    PUB_KEY = f.read()


HOSTNAME = "http://localhost:8081/"
USERNAME = "journalist"
PASSWORD = "correct horse battery staple profanity oil chewy"
TOTP = pyotp.TOTP("JHCOGO7VCER3EJ4L")

# Time (in milliseconds) to wait for these GUI elements to render.
TIME_APP_START = 1000
TIME_LOGIN = 10000
TIME_LOGOUT = 10000
TIME_SYNC = 10000
TIME_CLICK_ACTION = 1000
TIME_RENDER_SOURCE_LIST = 20000
TIME_RENDER_CONV_VIEW = 1000
TIME_RENDER_EXPORT_WIZARD = 1000
TIME_FILE_DOWNLOAD = 5000
TIME_KEYCLICK_ACTION = 5000


@pytest.fixture
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


@pytest.fixture
def print_dialog(request, mocker):
    """
    Fixture that returns a print dialog. Tests using this fixture must
    pass a parametrized string representing the result of the (simulated)
    qrexec print command. Acceptable values are ExportStatus enum values
    ("ExportStatus.SAMPLE.value"), but arbitrary strings can be supplied in
    order to simulate unexpected/malformed results.
    See tests/conversation/export/test_print_dialog.py.
    """
    mocker.patch("PyQt5.QtWidgets.QApplication.activeWindow", return_value=QMainWindow())
    export = _stub_export(mocker, status_string=request.param)

    return conversation.PrintDialog(export, "file123.jpg", ["/mock/path/to/file"])


def _stub_export(mocker, status_string=None):
    """
    Helper. Return an Export instance that mocks out QProcess calls to qrexec,
    returning a string instead of executing the process.

    The string is supplied as an indirect parameter in the calling test method.
    Under normal circumstances, it should be an ExportStatus value;
    for testing purposes, allow any arbitrary string in order to test exception
    handling between export.py and the print dialog on invalid input.
    """
    export = Export()
    export.process = mocker.MagicMock()

    # Simulate qrexec return value, which is printed to stderr
    # and then captured by QProcess. See export.py
    export.process.readAllStandardError = mocker.MagicMock()
    export.process.readAllStandardError.return_value.data = mocker.MagicMock()
    if status_string:
        export.process.readAllStandardError.return_value.data.return_value = status_string.encode(
            "utf-8"
        )

    mocker.patch.object(export, "_run_qrexec_export")
    mocker.patch.object(export, "_create_archive")

    return export


@pytest.fixture
def export_wizard_multifile(mocker, homedir):
    mocker.patch("PyQt5.QtWidgets.QApplication.activeWindow", return_value=QMainWindow())

    export_device = mocker.MagicMock(spec=Export)

    return conversation.ExportWizard(
        export_device,
        "3 files",
        ["/some/path/file123.jpg", "/some/path/memo.txt", "/some/path/transcript.txt"],
    )


@pytest.fixture
def export_wizard(mocker, homedir):
    mocker.patch("PyQt5.QtWidgets.QApplication.activeWindow", return_value=QMainWindow())

    export_device = mocker.MagicMock(spec=Export)

    return conversation.ExportWizard(export_device, "file123.jpg", ["/mock/path/to/file"])


@pytest.fixture
def export_transcript_wizard(mocker, homedir):
    mocker.patch("PyQt5.QtWidgets.QApplication.activeWindow", return_value=QMainWindow())

    export_device = mocker.MagicMock(spec=Export)

    return conversation.ExportWizard(export_device, "transcript.txt", ["/some/path/transcript.txt"])


@pytest.fixture
def i18n():
    """
    Set up locale/language/gettext functions. This enables the use of _().
    """
    configure_locale_and_language()


@pytest.fixture
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

    return tmpdir


@pytest.fixture
def mock_export_locked():
    """
    Represents the following scenario:
        * No USB
        * Export wizard launched
        * USB inserted
        * Passphrase successfully entered on first attempt (and export suceeeds)
    """
    device = Export()
    status = iter(
        [
            ExportStatus.NO_DEVICE_DETECTED,
            ExportStatus.DEVICE_LOCKED,
            ExportStatus.SUCCESS_EXPORT,
        ]
    )

    def get_status() -> ExportStatus:
        return next(status)

    device.run_export_preflight_checks = lambda: device.export_state_changed.emit(
        ExportStatus.NO_DEVICE_DETECTED
    )
    device.run_printer_preflight_checks = lambda: None
    device.print = lambda filepaths: None
    device.export = lambda filepaths, passphrase: device.export_state_changed.emit(get_status())

    return device


@pytest.fixture
def mock_export_unlocked():
    """
    Represents the following scenario:
        * USB already inserted and unlocked by the user
        * Export wizard launched
        * Export succeeds
    """
    device = Export()

    device.run_export_preflight_checks = lambda: device.export_state_changed.emit(
        ExportStatus.DEVICE_WRITABLE
    )
    device.run_printer_preflight_checks = lambda: None
    device.print = lambda filepaths: None
    device.export = lambda filepaths, passphrase: device.export_state_changed.emit(
        ExportStatus.SUCCESS_EXPORT
    )

    return device


@pytest.fixture
def mock_export_no_usb_then_bad_passphrase():
    """
    Represents the following scenario:
        * Export wizard launched
        * Locked USB detected
        * Mistyped Passphrase
        * Correct passphrase
        * Export succeeds
    """
    device = Export()
    status = iter(
        [
            ExportStatus.NO_DEVICE_DETECTED,
            ExportStatus.DEVICE_LOCKED,
            ExportStatus.ERROR_UNLOCK_LUKS,
            ExportStatus.SUCCESS_EXPORT,
        ]
    )

    def get_status() -> ExportStatus:
        return next(status)

    device.run_export_preflight_checks = lambda: device.export_state_changed.emit(
        ExportStatus.NO_DEVICE_DETECTED
    )
    device.run_printer_preflight_checks = lambda: None
    device.print = lambda filepaths: None
    device.export = lambda filepaths, passphrase: device.export_state_changed.emit(get_status())

    return device


@pytest.fixture
def mock_export_fail_early():
    """
    Represents the following scenario:
        * No USB inserted
        * Export wizard launched
        * Locked USB inserted
        * Unrecoverable error before export happens
          (eg, mount error)
    """
    device = Export()
    # why does it need an extra ERROR_MOUNT report?
    status = iter(
        [
            ExportStatus.NO_DEVICE_DETECTED,
            ExportStatus.DEVICE_LOCKED,
            ExportStatus.ERROR_MOUNT,
        ]
    )

    def get_status() -> ExportStatus:
        return next(status)

    device.run_export_preflight_checks = lambda: device.export_state_changed.emit(
        ExportStatus.NO_DEVICE_DETECTED
    )
    device.run_printer_preflight_checks = lambda: None
    device.print = lambda filepaths: None
    device.export = lambda filepaths, passphrase: device.export_state_changed.emit(get_status())

    return device


@pytest.fixture
def functional_test_app_started_context(
    vcr_api, homedir, reply_status_codes, session, config, qtbot
):
    """
    Returns a tuple containing the gui window and controller of a configured client. This should be
    used to for tests that need to start from the login dialog before the main application window
    is visible.
    """
    app_state = state.State()
    gui = Window(app_state)
    create_gpg_test_context(homedir)  # Configure test keys
    session_maker = make_session_maker(homedir)  # Configure and create the database
    controller = Controller(HOSTNAME, gui, session_maker, homedir, app_state, False, False)
    gui.setup(controller)  # Connect the gui to the controller

    def login_dialog_is_visible():
        assert gui.login_dialog is not None

    qtbot.waitUntil(login_dialog_is_visible, timeout=TIME_APP_START)

    return (gui, controller)


@pytest.fixture
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
    qtbot.keyClicks(gui.login_dialog.tfa_field, str(TOTP.now()))
    qtbot.mouseClick(gui.login_dialog.submit, Qt.LeftButton)
    qtbot.wait(TIME_CLICK_ACTION)

    def logged_in():
        assert gui.login_dialog is None
        assert gui.isVisible()

    qtbot.waitUntil(logged_in, timeout=TIME_LOGIN)

    return (gui, controller)


@pytest.fixture
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
    gui.left_pane.user_profile.user_button._menu.logout.trigger()

    def check_login_button():
        assert gui.left_pane.user_profile.login_button.isVisible()

    # When the login button appears then we know we're now in offline mode
    qtbot.waitUntil(check_login_button, timeout=TIME_LOGOUT)

    return (gui, controller)


@pytest.fixture
def config(homedir) -> str:
    os.environ["SD_SUBMISSION_KEY_FPR"] = "65A1B5FF195B56353CC63DFFCC40EF1228271441"


@pytest.fixture
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


@pytest.fixture
def session_maker(homedir):
    return make_session_maker(homedir)


@pytest.fixture
def session(session_maker):
    sess = session_maker
    Base.metadata.create_all(bind=sess.get_bind(), checkfirst=False)
    yield sess
    sess.close()


@pytest.fixture
def reply_status_codes(session) -> None:
    for reply_send_status in ReplySendStatusCodes:
        reply_status = ReplySendStatus(reply_send_status.value)
        session.add(reply_status)
        session.commit()


@pytest.fixture
def download_error_codes(session) -> None:
    for download_error_code in DownloadErrorCodes:
        download_error = DownloadError(download_error_code.name)
        session.add(download_error)
        session.commit()


@pytest.fixture
def source(session) -> dict:
    args = {"uuid": str(uuid4()), "public_key": PUB_KEY}
    source = Source(
        journalist_designation="foo-bar",
        is_flagged=False,
        interaction_count=0,
        is_starred=False,
        last_updated=datetime.now(),
        document_count=0,
        **args,
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
    result = subprocess.run(cmd, check=False)
    if result.returncode != 0:
        raise RuntimeError(
            f"Unable to import test GPG key. STDOUT: {result.stdout} STDERR: {result.stderr}"
        )


@pytest.fixture
def vcr_api(request):
    module_group = request.module.__name__.split(".")[1]
    library = vcr.VCR(cassette_library_dir=f"tests/{module_group}/data/")
    context = library.use_cassette(f"{request.function.__name__}.yml")
    # Override `Cassette` to use our subclass before we enter the
    # context manager.
    context.cls = Cassette
    with context as cassette:

        def create(*args, **kwargs):
            api = VCRAPI(*args, **kwargs)
            api._cassette = cassette
            return api

        with mock.patch("securedrop_client.sdk.API", new=create):
            yield
