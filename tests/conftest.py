import json
import os
import pytest

from datetime import datetime
from securedrop_client.config import Config
from securedrop_client.models import Base, make_engine, Source
from sqlalchemy.orm import sessionmaker
from uuid import uuid4


with open(os.path.join(os.path.dirname(__file__), 'files', 'test-key.gpg.pub.asc')) as f:
    PUB_KEY = f.read()


@pytest.fixture(scope='function')
def safe_tmpdir(tmpdir):
    os.chmod(str(tmpdir), 0o0700)
    return tmpdir


@pytest.fixture(scope='function')
def config(safe_tmpdir) -> str:
    full_path = str(safe_tmpdir.join(Config.CONFIG_NAME))
    with open(full_path, 'w') as f:
        f.write(json.dumps({
            'journalist_key_fingerprint': '65A1B5FF195B56353CC63DFFCC40EF1228271441',
        }))
    return full_path


@pytest.fixture(scope='function')
def session(safe_tmpdir):
    engine = make_engine(str(safe_tmpdir))
    Base.metadata.create_all(bind=engine)
    Session = sessionmaker(bind=engine)
    session = Session()
    return session


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
    session.add(source)
    session.commit()
    args['id'] = source.id
    args['source'] = source
    return args
