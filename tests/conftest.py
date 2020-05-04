import json
import os
import tempfile
import pytest
import subprocess

from configparser import ConfigParser
from datetime import datetime

from PyQt5.QtCore import Qt

from securedrop_client.gui.main import Window
from securedrop_client.logic import Controller
from securedrop_client.config import Config
from securedrop_client.app import configure_locale_and_language
from securedrop_client.db import (
    Base, DownloadError, DownloadErrorCodes, ReplySendStatus,
    ReplySendStatusCodes, Source, make_session_maker
)
from uuid import uuid4


with open(os.path.join(os.path.dirname(__file__), 'files', 'test-key.gpg.pub.asc')) as f:
    PUB_KEY = f.read()


HOSTNAME = "http://localhost:8081/"
USERNAME = "journalist"
PASSWORD = "correct horse battery staple profanity oil chewy"

# Modify cassettes to use the following TOTP code. For developing new tests,
# you can modify this so you don't need to keep editing cassettes during
# development.
TOTP = "994892"


@pytest.fixture(scope='function')
def i18n():
    '''
    Set up locale/language/gettext functions. This enables the use of _().
    '''
    configure_locale_and_language()


@pytest.fixture(scope='function')
def homedir(i18n):
    '''
    Create a "homedir" for a client.

    Using `mkdtemp` and not `TemporaryDirectory` because the latter will remove the directory
    when the object is destroyed, and we want to leave it on the file system so developers can
    inspect the contents for debugging purposes.
    '''

    tmpdir = tempfile.mkdtemp(prefix='sdc-')
    os.chmod(tmpdir, 0o0700)

    data_dir = os.path.join(tmpdir, 'data')
    gpg_dir = os.path.join(tmpdir, 'gpg')
    logs_dir = os.path.join(tmpdir, 'logs')

    for dir_ in [data_dir, gpg_dir, logs_dir]:
        os.mkdir(dir_)
        os.chmod(dir_, 0o0700)

    yield tmpdir


@pytest.fixture(scope='function')
def functional_test_logged_out_context(homedir, reply_status_codes, session, config):
    '''
    Returns a tuple containing a Window instance and a Controller instance that
    have been correctly set up and isolated from any other instances of the
    application to be run in the test suite.
    '''

    gui = Window()
    # Configure test keys.
    create_gpg_test_context(homedir)

    # Configure and create the database.
    session_maker = make_session_maker(homedir)

    # Create the controller.
    controller = Controller(HOSTNAME, gui, session_maker, homedir,
                            False, False)
    # Link the gui and controller together.
    gui.controller = controller
    # Et Voila...
    return (gui, controller, homedir)


@pytest.fixture(scope='function')
def functional_test_logged_in_context(functional_test_logged_out_context, qtbot):
    """
    Returns a tuple containing a Window and Controller instance that have been
    correctly configured to work together, isolated from other runs of the
    test suite and in a logged in state.
    """
    gui, controller, tempdir = functional_test_logged_out_context
    gui.setup(controller)
    qtbot.keyClicks(gui.login_dialog.username_field, USERNAME)
    qtbot.keyClicks(gui.login_dialog.password_field, PASSWORD)
    qtbot.keyClicks(gui.login_dialog.tfa_field, TOTP)
    qtbot.mouseClick(gui.login_dialog.submit, Qt.LeftButton)

    def wait_for_login():
        assert gui.login_dialog is None

    qtbot.waitUntil(wait_for_login, timeout=10000)
    return (gui, controller, homedir)


@pytest.fixture(scope='function')
def config(homedir) -> str:
    full_path = os.path.join(homedir, Config.CONFIG_NAME)
    with open(full_path, 'w') as f:
        f.write(json.dumps({
            'journalist_key_fingerprint': '65A1B5FF195B56353CC63DFFCC40EF1228271441',
        }))
    return full_path


@pytest.fixture(scope='function')
def alembic_config(homedir):
    return _alembic_config(homedir)


def _alembic_config(homedir):
    base_dir = os.path.join(os.path.dirname(__file__), '..')
    migrations_dir = os.path.join(base_dir, 'alembic')
    ini = ConfigParser()
    ini.read(os.path.join(base_dir, 'alembic.ini'))

    ini.set('alembic', 'script_location', os.path.join(migrations_dir))
    ini.set('alembic', 'sqlalchemy.url',
            'sqlite:///{}'.format(os.path.join(homedir, 'svs.sqlite')))

    alembic_path = os.path.join(homedir, 'alembic.ini')

    with open(alembic_path, 'w') as f:
        ini.write(f)

    return alembic_path


@pytest.fixture(scope='function')
def session_maker(homedir):
    return make_session_maker(homedir)


@pytest.fixture(scope='function')
def session(session_maker):
    sess = session_maker
    Base.metadata.create_all(bind=sess.get_bind(), checkfirst=False)
    yield sess
    sess.close()


@pytest.fixture(scope='function')
def reply_status_codes(session) -> None:
    for reply_send_status in ReplySendStatusCodes:
        reply_status = ReplySendStatus(reply_send_status.value)
        session.add(reply_status)
        session.commit()
    return


@pytest.fixture(scope='function')
def download_error_codes(session) -> None:
    for download_error_code in DownloadErrorCodes:
        download_error = DownloadError(download_error_code.name)
        session.add(download_error)
        session.commit()
    return


@pytest.fixture(scope='function')
def source(session) -> dict:
    args = {
        'uuid': str(uuid4()),
        'public_key': PUB_KEY,
    }
    source = Source(journalist_designation='foo-bar',
                    is_flagged=False,
                    interaction_count=0,
                    is_starred=False,
                    last_updated=datetime.now(),
                    document_count=0,
                    **args)
    args['fingerprint'] = source.fingerprint = 'B2FF7FB28EED8CABEBC5FB6C6179D97BCFA52E5F'
    session.add(source)
    session.commit()
    args['id'] = source.id
    args['source'] = source
    return args


def create_gpg_test_context(sdc_home):
    """
    Ensures the correct key is in the $sdc_home/gpg directory. Needs the
    gpg command to be installed for this to work.
    """
    gpg_home = os.path.join(sdc_home, "gpg")
    func_test_path = os.path.dirname(os.path.abspath(__file__))
    key_file = os.path.join(func_test_path, "files",
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
