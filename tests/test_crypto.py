import os
import pytest

from subprocess import CalledProcessError
from uuid import uuid4

from securedrop_client.crypto import GpgHelper, CryptoError

with open(os.path.join(os.path.dirname(__file__), 'files', 'test-key.gpg.pub.asc')) as f:
    PUB_KEY = f.read()


def test_message_logic(safe_tmpdir, mocker):
    """
    Ensure that messages are handled
    """
    gpg = GpgHelper(str(safe_tmpdir), is_qubes=False)

    # Make data dir since we do need it for this test
    data_dir = safe_tmpdir.mkdir('data')
    os.chmod(str(data_dir), 0o700)

    test_msg = 'tests/files/test-msg.gpg'
    expected_output_filename = 'test-msg'

    mock_gpg = mocker.patch('subprocess.call', return_value=0)
    mocker.patch('os.unlink')

    dest = gpg.decrypt_submission_or_reply(test_msg, expected_output_filename, is_doc=False)

    assert mock_gpg.call_count == 1
    assert dest == '{}/data/{}'.format(
        str(safe_tmpdir), expected_output_filename)


def test_gunzip_logic(safe_tmpdir, mocker):
    """
    Ensure that gzipped documents/files are handled
    """
    gpg = GpgHelper(str(safe_tmpdir), is_qubes=False)

    # Make data dir since we do need it for this test
    data_dir = safe_tmpdir.mkdir('data')
    os.chmod(str(data_dir), 0o700)

    test_gzip = 'tests/files/test-doc.gz.gpg'
    expected_output_filename = 'test-doc'

    mock_gpg = mocker.patch('subprocess.call', return_value=0)
    mocker.patch('os.unlink')
    dest = gpg.decrypt_submission_or_reply(test_gzip, expected_output_filename, is_doc=True)

    assert mock_gpg.call_count == 1
    assert dest == '{}/data/{}'.format(
        str(safe_tmpdir), expected_output_filename)


def test_subprocess_raises_exception(safe_tmpdir, mocker):
    """
    Ensure that failed GPG commands raise an exception.
    """
    gpg = GpgHelper(str(safe_tmpdir), is_qubes=False)

    # Make data dir since we do need it for this test
    data_dir = safe_tmpdir.mkdir('data')
    os.chmod(str(data_dir), 0o700)

    test_gzip = 'tests/files/test-doc.gz.gpg'
    output_filename = 'test-doc'

    mock_gpg = mocker.patch('subprocess.call', return_value=1)
    mocker.patch('os.unlink')

    with pytest.raises(CryptoError):
        gpg.decrypt_submission_or_reply(test_gzip, output_filename, is_doc=True)

    assert mock_gpg.call_count == 1


def test_import_key(safe_tmpdir, source):
    '''
    Check the happy path that we can import a single PGP key.
    '''
    helper = GpgHelper(str(safe_tmpdir), is_qubes=False)
    helper.import_key(source['uuid'], source['public_key'])


def test_import_key_gpg_call_fail(safe_tmpdir, mocker):
    '''
    Check that a `CryptoError` is raised if calling `gpg` fails.
    '''
    helper = GpgHelper(str(safe_tmpdir), is_qubes=False)
    err = CalledProcessError(cmd=['foo'], returncode=1)
    mock_call = mocker.patch('securedrop_client.crypto.subprocess.check_call',
                             side_effect=err)

    with pytest.raises(CryptoError, match='Could not import key\\.'):
        helper._import(PUB_KEY)

    # ensure the mock was used
    assert mock_call.called


def test_import_key_multiple_fingerprints(safe_tmpdir, source, mocker):
    '''
    Check that an error is raised if multiple fingerpints are found on key import.
    '''
    helper = GpgHelper(str(safe_tmpdir), is_qubes=False)
    mock_import = mocker.patch.object(helper, '_import', returnvalue={'a', 'b'})

    with pytest.raises(RuntimeError, match='Expected exactly one fingerprint\\.'):
        helper.import_key(source['uuid'], source['public_key'])

    # ensure the mock was used
    assert mock_import.called
