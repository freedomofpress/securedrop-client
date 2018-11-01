import os
import pytest
from datetime import datetime
from sqlalchemy.orm import sessionmaker
from uuid import uuid4

from securedrop_client.models import Base, make_engine, Source

with open(os.path.join(os.path.dirname(__file__), 'keys',
                       'test-key.gpg.pub.asc')) as f:
    PUB_KEY = f.read()


@pytest.fixture(scope='function')
def safe_tmpdir(tmpdir):
    os.chmod(str(tmpdir), 0o0700)
    return tmpdir


@pytest.fixture(scope='function')
def db_session(safe_tmpdir):
    engine = make_engine(str(safe_tmpdir))
    session = sessionmaker(bind=engine)()
    Base.metadata.create_all(engine)
    return session


@pytest.fixture(scope='function')
def source(db_session) -> dict:
    source = Source(uuid=str(uuid4()),
                    journalist_designation='testy-mctestface',
                    is_flagged=False,
                    public_key=PUB_KEY,
                    interaction_count=1,
                    is_starred=False,
                    last_updated=datetime.now())
    db_session.add(source)
    db_session.commit()
    return {
        'id': source.id,
        'uuid': source.uuid,
    }
