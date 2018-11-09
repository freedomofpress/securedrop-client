import os
import pytest
from os import path
from securedrop_client.crypto import GpgHelper, CryptoException
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
    gpg = GpgHelper(str(safe_tmpdir), mock.MagicMock(), is_qubes=False)
    gpg.import_key(source['uuid'], PRIV_KEY)
    gpg.import_key(source['uuid'], PUB_KEY)

    assert gpg.gpg.list_keys(secret=False)
    assert gpg.gpg.list_keys(secret=True)


def test_key_import_failures(safe_tmpdir, db_session, source):
    '''Simple test to ensure we can import keys.'''
    gpg = GpgHelper(str(safe_tmpdir), db_session, is_qubes=False)
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
    gpg = GpgHelper(gpg_home, db_session, is_qubes=False)
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
    gpg = GpgHelper(gpg_home, db_session, is_qubes=False)
    gpg.import_key(source['uuid'], PUB_KEY)

    mock_ret = mock.MagicMock()
    mock_ret.ok = False
    with mock.patch.object(gpg.gpg, 'encrypt', return_value=mock_ret):
        with pytest.raises(RuntimeError):
            plaintext = 'sekrit mesidge'
            cyphertext = gpg.encrypt_to_source(source['uuid'], plaintext)


def test_repr():
    with mock.patch('securedrop_client.crypto.GPG'):
        gpg = GpgHelper(mock.MagicMock(), mock.MagicMock(), is_qubes=False)
        assert isinstance(gpg.__repr__(), str)


def test_gunzip_logic(safe_tmpdir):
    """
    Ensure that gzipped documents/files are handled
    """
    data_dir = str(safe_tmpdir.mkdir('data'))
    gpg_dir = str(safe_tmpdir.mkdir('gpg'))
    os.chmod(data_dir, 0o700)
    os.chmod(gpg_dir, 0o700)

    gpg = GpgHelper(gpg_dir, mock.MagicMock(), is_qubes=False)

    test_gzip = 'tests/files/test-doc.gz.gpg'
    expected_output_filename = 'test-doc'

    with mock.patch.object(gpg.gpg, 'decrypt_file') as mock_gpg, \
            mock.patch('os.unlink') as mock_unlink:
        dest = gpg.decrypt_submission_or_reply(
            test_gzip, expected_output_filename,
            is_doc=True)

    assert mock_gpg.call_count == 1
    assert dest == '{}/data/{}'.format(
        str(safe_tmpdir), expected_output_filename)


def test_decrypt_failure(safe_tmpdir):
    gpg = GpgHelper(str(safe_tmpdir), mock.MagicMock(), is_qubes=False)
    mock_ret = mock.MagicMock()
    mock_ret.__bool__ = lambda x: False
    mock.status = 'oh nein :('
    with mock.patch.object(gpg.gpg, 'decrypt_file', return_value=mock_ret), \
            mock.patch('os.unlink'), \
            pytest.raises(CryptoException):
        gpg.decrypt_submission_or_reply('', '', False)


def test_decrypt_message(safe_tmpdir):
    data_dir = str(safe_tmpdir.mkdir('data'))
    gpg_dir = str(safe_tmpdir.mkdir('gpg'))
    os.chmod(data_dir, 0o700)
    os.chmod(gpg_dir, 0o700)

    test_file = os.path.join(data_dir, 'dummy')
    test_file_name = 'foo'
    open(test_file, 'w').close()  # create the file

    gpg = GpgHelper(gpg_dir, mock.MagicMock(), is_qubes=False)

    with mock.patch.object(gpg.gpg, 'decrypt_file') as mock_decrypt:
        gpg.decrypt_submission_or_reply(test_file, test_file_name, False)

    assert os.path.isfile(path.join(data_dir, test_file_name))
    assert not os.path.exists(test_file)
    assert mock_decrypt.called
