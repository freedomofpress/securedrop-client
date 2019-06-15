import os
import subprocess
import pytest

from subprocess import CalledProcessError

from securedrop_client.crypto import GpgHelper, CryptoError

with open(os.path.join(os.path.dirname(__file__), 'files', 'test-key.gpg.pub.asc')) as f:
    PUB_KEY = f.read()

with open(os.path.join(os.path.dirname(__file__), 'files', 'securedrop.gpg.asc')) as f:
    JOURNO_KEY = f.read()


def test_message_logic(homedir, config, mocker, session_maker):
    """
    Ensure that messages are handled.
    Using the `config` fixture to ensure the config is written to disk.
    """
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)

    test_msg = 'tests/files/test-msg.gpg'
    expected_output_filepath = os.path.join(homedir, 'data', 'test-msg')

    mock_gpg = mocker.patch('subprocess.call', return_value=0)
    mocker.patch('os.unlink')

    dest = gpg.decrypt_submission_or_reply(test_msg, expected_output_filepath, is_doc=False)

    assert mock_gpg.call_count == 1
    assert dest == expected_output_filepath


def test_gunzip_logic(homedir, config, mocker, session_maker):
    """
    Ensure that gzipped documents/files are handled
    Using the `config` fixture to ensure the config is written to disk.
    """
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)

    test_gzip = 'tests/files/test-doc.gz.gpg'
    expected_output_filepath = os.path.join(homedir, 'data', 'mock-doc')

    mock_gpg = mocker.patch('subprocess.call', return_value=0)
    mock_unlink = mocker.patch('os.unlink')
    dest = gpg.decrypt_submission_or_reply(test_gzip, expected_output_filepath, is_doc=True)

    assert mock_gpg.call_count == 1
    assert dest == expected_output_filepath
    # We should remove two files in the success scenario: err, filepath
    assert mock_unlink.call_count == 2


def test_subprocess_raises_exception(homedir, config, mocker, session_maker):
    """
    Ensure that failed GPG commands raise an exception.
    Using the `config` fixture to ensure the config is written to disk.
    """
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)

    test_gzip = 'tests/files/test-doc.gz.gpg'
    output_filename = 'test-doc'

    mock_gpg = mocker.patch('subprocess.call', return_value=1)
    mock_unlink = mocker.patch('os.unlink')

    with pytest.raises(CryptoError):
        gpg.decrypt_submission_or_reply(test_gzip, output_filename, is_doc=True)

    assert mock_gpg.call_count == 1
    # We should only remove one file in the failure scenario: err
    assert mock_unlink.call_count == 1


def test_import_key(homedir, config, source, session_maker):
    '''
    Check the happy path that we can import a single PGP key.
    Using the `config` fixture to ensure the config is written to disk.
    '''
    helper = GpgHelper(homedir, session_maker, is_qubes=False)
    helper.import_key(source['uuid'], source['public_key'], source['fingerprint'])


def test_import_key_gpg_call_fail(homedir, config, mocker, session_maker):
    '''
    Check that a `CryptoError` is raised if calling `gpg` fails.
    Using the `config` fixture to ensure the config is written to disk.
    '''
    helper = GpgHelper(homedir, session_maker, is_qubes=False)
    err = CalledProcessError(cmd=['foo'], returncode=1)
    mock_call = mocker.patch('securedrop_client.crypto.subprocess.check_call',
                             side_effect=err)

    with pytest.raises(CryptoError, match='Could not import key\\.'):
        helper._import(PUB_KEY)

    # ensure the mock was used
    assert mock_call.called


def test_encrypt(homedir, source, config, mocker, session_maker):
    '''
    Check that calling `encrypt` encrypts the message.
    Using the `config` fixture to ensure the config is written to disk.
    '''
    helper = GpgHelper(homedir, session_maker, is_qubes=False)

    # first we have to ensure the pubkeys are available
    helper._import(PUB_KEY)
    helper._import(JOURNO_KEY)

    plaintext = 'bueller?'
    cyphertext = helper.encrypt_to_source(source['uuid'], plaintext)

    # check that we go *any* output just for sanity
    assert cyphertext

    cyphertext_file = os.path.join(homedir, 'cyphertext.out')
    decrypted_file = os.path.join(homedir, 'decrypted.out')
    gpg_home = os.path.join(homedir, 'gpg')

    with open(cyphertext_file, 'w') as f:
        f.write(cyphertext)

    subprocess.check_call(['gpg',
                           '--homedir', gpg_home,
                           '--output', decrypted_file,
                           '--decrypt', cyphertext_file])

    with open(decrypted_file) as f:
        decrypted = f.read()

    assert decrypted == plaintext


def test_encrypt_fail(homedir, source, config, mocker, session_maker):
    '''
    Check that a `CryptoError` is raised if the call to `gpg` fails.
    Using the `config` fixture to ensure the config is written to disk.
    '''
    helper = GpgHelper(homedir, session_maker, is_qubes=False)

    # first we have to ensure the pubkeys are available
    helper._import(PUB_KEY)

    plaintext = 'bueller?'

    err = CalledProcessError(cmd=['foo'], returncode=1)
    mock_gpg = mocker.patch('securedrop_client.crypto.subprocess.check_call',
                            side_effect=err)

    with pytest.raises(CryptoError):
        helper.encrypt_to_source(source['uuid'], plaintext)

    # check mock called to prevent "dead code"
    assert mock_gpg.called
