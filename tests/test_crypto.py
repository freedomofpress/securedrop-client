import os
import pytest

from unittest import mock

from securedrop_client.crypto import GpgHelper, CryptoError


def test_message_logic(safe_tmpdir):
    """
    Ensure that messages are handled
    """
    gpg = GpgHelper(str(safe_tmpdir), is_qubes=False)

    # Make data dir since we do need it for this test
    data_dir = safe_tmpdir.mkdir('data')
    os.chmod(str(data_dir), 0o700)

    test_msg = 'tests/files/test-msg.gpg'
    expected_output_filename = 'test-msg'

    with mock.patch('subprocess.call',
                    return_value=0) as mock_gpg, \
            mock.patch('os.unlink'):
        dest = gpg.decrypt_submission_or_reply(
            test_msg, expected_output_filename, is_doc=False)

    assert mock_gpg.call_count == 1
    assert dest == '{}/data/{}'.format(
        str(safe_tmpdir), expected_output_filename)


def test_gunzip_logic(safe_tmpdir):
    """
    Ensure that gzipped documents/files are handled
    """
    gpg = GpgHelper(str(safe_tmpdir), is_qubes=False)

    # Make data dir since we do need it for this test
    data_dir = safe_tmpdir.mkdir('data')
    os.chmod(str(data_dir), 0o700)

    test_gzip = 'tests/files/test-doc.gz.gpg'
    expected_output_filename = 'test-doc'

    with mock.patch('subprocess.call',
                    return_value=0) as mock_gpg, \
            mock.patch('os.unlink'):
        dest = gpg.decrypt_submission_or_reply(
            test_gzip, expected_output_filename, is_doc=True)

    assert mock_gpg.call_count == 1
    assert dest == '{}/data/{}'.format(
        str(safe_tmpdir), expected_output_filename)


def test_subprocess_raises_exception(safe_tmpdir):
    """
    Ensure that failed GPG commands raise an exception.
    """
    gpg = GpgHelper(str(safe_tmpdir), is_qubes=False)

    # Make data dir since we do need it for this test
    data_dir = safe_tmpdir.mkdir('data')
    os.chmod(str(data_dir), 0o700)

    test_gzip = 'tests/files/test-doc.gz.gpg'
    output_filename = 'test-doc'

    with mock.patch('subprocess.call',
                    return_value=1) as mock_gpg, \
            mock.patch('os.unlink'):
        with pytest.raises(CryptoError):
            gpg.decrypt_submission_or_reply(test_gzip, output_filename, is_doc=True)

    assert mock_gpg.call_count == 1
