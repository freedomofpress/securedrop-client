import os

from securedrop_client.api_jobs.sync import MetadataSyncJob
from securedrop_client.crypto import GpgHelper, CryptoError

with open(os.path.join(os.path.dirname(__file__), '..', 'files', 'test-key.gpg.pub.asc')) as f:
    PUB_KEY = f.read()


def test_MetadataSyncJob_success(mocker, homedir, session, session_maker):
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = MetadataSyncJob(homedir, gpg)

    mock_source = mocker.MagicMock()
    mock_source.uuid = 'bar'
    mock_source.key = {
        'type': 'PGP',
        'public': PUB_KEY,
        'fingerprint': '123456ABC',
    }

    mock_key_import = mocker.patch.object(job.gpg, 'import_key')
    mock_get_remote_data = mocker.patch(
        'securedrop_client.api_jobs.sync.get_remote_data',
        return_value=([mock_source], 'submissions', 'replies'))

    api_client = mocker.MagicMock()
    api_client.default_request_timeout = mocker.MagicMock()
    api_client.default_request_timeout = mocker.MagicMock()

    mocker.patch(
        'securedrop_client.api_jobs.sync.update_local_storage',
        return_value=([mock_source], 'submissions', 'replies'))

    job.call_api(api_client, session)

    assert mock_key_import.call_args[0][0] == mock_source.uuid
    assert mock_key_import.call_args[0][1] == mock_source.key['public']
    assert mock_key_import.call_args[0][2] == mock_source.key['fingerprint']
    assert mock_get_remote_data.call_count == 1


def test_MetadataSyncJob_success_with_key_import_fail(mocker, homedir, session, session_maker):
    """
    Check that we can gracefully handle a key import failure.
    """
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = MetadataSyncJob(homedir, gpg)

    mock_source = mocker.MagicMock()
    mock_source.uuid = 'bar'
    mock_source.key = {
        'type': 'PGP',
        'public': PUB_KEY,
        'fingerprint': '123456ABC',
    }

    mock_key_import = mocker.patch.object(job.gpg, 'import_key',
                                          side_effect=CryptoError)
    mock_get_remote_data = mocker.patch(
        'securedrop_client.api_jobs.sync.get_remote_data',
        return_value=([mock_source], 'submissions', 'replies'))

    api_client = mocker.MagicMock()
    api_client.default_request_timeout = mocker.MagicMock()

    mocker.patch(
        'securedrop_client.api_jobs.sync.update_local_storage',
        return_value=([mock_source], 'submissions', 'replies'))

    job.call_api(api_client, session)

    assert mock_key_import.call_args[0][0] == mock_source.uuid
    assert mock_key_import.call_args[0][1] == mock_source.key['public']
    assert mock_key_import.call_args[0][2] == mock_source.key['fingerprint']
    assert mock_get_remote_data.call_count == 1


def test_MetadataSyncJob_success_with_missing_key(mocker, homedir, session, session_maker):
    """
    Check that we can gracefully handle missing source keys.
    """
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = MetadataSyncJob(homedir, gpg)

    mock_source = mocker.MagicMock()
    mock_source.uuid = 'bar'
    mock_source.key = {
        'type': 'PGP',
        'pub_key': '',
        'fingerprint': ''
    }

    mock_key_import = mocker.patch.object(job.gpg, 'import_key')
    mock_get_remote_data = mocker.patch(
        'securedrop_client.api_jobs.sync.get_remote_data',
        return_value=([mock_source], 'submissions', 'replies'))

    api_client = mocker.MagicMock()
    api_client.default_request_timeout = mocker.MagicMock()

    mocker.patch(
        'securedrop_client.api_jobs.sync.update_local_storage',
        return_value=([mock_source], 'submissions', 'replies'))

    job.call_api(api_client, session)

    assert mock_key_import.call_count == 0
    assert mock_get_remote_data.call_count == 1
