import pytest
import os
from unittest import mock

from securedrop_client.crypto import decrypt_submission


def test_gunzip_logic(safe_tmpdir):
    """
    Ensure that gzipped documents/files are handled
    """
    # Make data dir since we do need it for this test
    data_dir = os.path.join(str(safe_tmpdir), 'data')
    if not os.path.exists(data_dir):
        os.makedirs(data_dir)

    test_gzip = 'tests/files/test-doc.gz.gpg'
    expected_output_filename = 'test-doc'

    with mock.patch('subprocess.call',
                    return_value=0) as mock_gpg, \
            mock.patch('os.unlink') as mock_unlink:
        res, dest = decrypt_submission(
            test_gzip, expected_output_filename,
            str(safe_tmpdir), is_qubes=False,
            is_doc=True)

    assert mock_gpg.call_count == 1
    assert res == 0
    assert dest == '{}/data/{}'.format(
        str(safe_tmpdir), expected_output_filename)
