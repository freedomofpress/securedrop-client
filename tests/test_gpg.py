import pytest
from os import path
from securedrop_client.gpg import GpgHelper
from securedrop_client.models import Source
from securedrop_client.utils import safe_mkdir
from unittest import mock
from uuid import uuid4

KEY_DIR = path.join(path.dirname(__file__), 'keys')

with open(path.join(KEY_DIR, 'test-key.gpg.asc')) as f:
    PRIV_KEY = f.read()

with open(path.join(KEY_DIR, 'test-key.gpg.pub.asc')) as f:
    PUB_KEY = f.read()


def test_key_import(safe_tmpdir, source):
    '''Simple test to ensure we can import keys.'''
    gpg = GpgHelper(str(safe_tmpdir), mock.MagicMock())
    gpg.import_key(source['uuid'], PRIV_KEY)
    gpg.import_key(source['uuid'], PUB_KEY)

    assert gpg.gpg.list_keys(secret=False)
    assert gpg.gpg.list_keys(secret=True)


def test_key_import_failures(safe_tmpdir, db_session, source):
    '''Simple test to ensure we can import keys.'''
    gpg = GpgHelper(str(safe_tmpdir), db_session)
    assert not gpg.gpg.list_keys(secret=False)  # precondition

    # import on non-existent source should fail
    with pytest.raises(RuntimeError):
        gpg.import_key(str(uuid4()), PUB_KEY)
    assert not gpg.gpg.list_keys(secret=False)

    # import fail
    mock_ret = mock.MagicMock()
    mock_ret.__bool__ = lambda x: False
    with mock.patch.object(gpg.gpg, 'import_keys', return_value=mock_ret):
        with pytest.raises(RuntimeError):
            gpg.import_key(source['uuid'], PUB_KEY)
    assert not gpg.gpg.list_keys(secret=False)

    # import multiple fingerprints
    mock_ret = mock.MagicMock()
    mock_ret.fingerprints = ['a', 'b']
    with mock.patch.object(gpg.gpg, 'import_keys', return_value=mock_ret):
        with pytest.raises(RuntimeError):
            gpg.import_key(source['uuid'], PUB_KEY)
    assert not gpg.gpg.list_keys(secret=False)


def test_encrypt(safe_tmpdir, db_session, source):
    safe_mkdir(str(safe_tmpdir), 'keys')
    gpg_home = path.join(str(safe_tmpdir), 'keys')
    gpg = GpgHelper(gpg_home, db_session)
    gpg.import_key(source['uuid'], PRIV_KEY)
    gpg.import_key(source['uuid'], PUB_KEY)

    plaintext = 'sekrit mesidge'
    cyphertext = gpg.encrypt_to_source(source['uuid'], plaintext)
    crypt = gpg.gpg.decrypt(cyphertext)
    assert crypt.ok
    decrypted = crypt.data.decode('utf-8')
    assert decrypted == plaintext


def test_encrypt_failure(safe_tmpdir, db_session, source):
    safe_mkdir(str(safe_tmpdir), 'keys')
    gpg_home = path.join(str(safe_tmpdir), 'keys')
    gpg = GpgHelper(gpg_home, db_session)
    gpg.import_key(source['uuid'], PUB_KEY)

    mock_ret = mock.MagicMock()
    mock_ret.ok = False
    with mock.patch.object(gpg.gpg, 'encrypt', return_value=mock_ret):
        with pytest.raises(RuntimeError):
            plaintext = 'sekrit mesidge'
            cyphertext = gpg.encrypt_to_source(source['uuid'], plaintext)


def test_key_import():
    '''Simple test to ensure we can import keys.'''
    with mock.patch('securedrop_client.gpg.GPG'):
        gpg = GpgHelper(mock.MagicMock(), mock.MagicMock())
        assert isinstance(gpg.__repr__(), str)
