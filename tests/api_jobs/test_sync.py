import os

from securedrop_client.api_jobs.sync import MetadataSyncJob
from securedrop_client.crypto import GpgHelper

from tests import factory


with open(os.path.join(os.path.dirname(__file__), '..', 'files', 'test-key.gpg.pub.asc')) as f:
    PUB_KEY = f.read()


def test_MetadataSyncJob_success(mocker, homedir, session, session_maker):
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = MetadataSyncJob(homedir, gpg)

    mock_source = factory.RemoteSource(
        key={
            'type': 'PGP',
            'public': PUB_KEY,
            'fingerprint': '123456ABC',
        }
    )

    mock_get_remote_data = mocker.patch(
        'securedrop_client.api_jobs.sync.get_remote_data',
        return_value=([mock_source], [], []))

    api_client = mocker.MagicMock()
    api_client.default_request_timeout = mocker.MagicMock()
    api_client.default_request_timeout = mocker.MagicMock()

    job.call_api(api_client, session)

    assert mock_get_remote_data.call_count == 1


def test_MetadataSyncJob_success_with_missing_key(mocker, homedir, session, session_maker):
    """
    Check that we can gracefully handle missing source keys.
    """
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = MetadataSyncJob(homedir, gpg)

    mock_source = factory.RemoteSource(
        key={
            'type': 'PGP',
            'public': '',
            'fingerprint': '',
        }
    )

    mock_key_import = mocker.patch.object(job.gpg, 'import_key')
    mock_get_remote_data = mocker.patch(
        'securedrop_client.api_jobs.sync.get_remote_data',
        return_value=([mock_source], [], []))

    api_client = mocker.MagicMock()
    api_client.default_request_timeout = mocker.MagicMock()

    job.call_api(api_client, session)

    assert mock_key_import.call_count == 0
    assert mock_get_remote_data.call_count == 1
