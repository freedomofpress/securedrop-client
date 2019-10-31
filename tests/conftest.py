import json
import os
import tempfile
import pytest

from configparser import ConfigParser
from datetime import datetime
from securedrop_client.config import Config
from securedrop_client.api_jobs.uploads import ReplySendStatusCodes
from securedrop_client.app import configure_locale_and_language
from securedrop_client.db import Base, make_session_maker, Source, ReplySendStatus
from uuid import uuid4


with open(os.path.join(os.path.dirname(__file__), 'files', 'test-key.gpg.pub.asc')) as f:
    PUB_KEY = f.read()


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
    sess = session_maker()
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
