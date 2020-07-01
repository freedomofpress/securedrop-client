import os

from securedrop_client.api_jobs.sync import MetadataSyncJob
from tests import factory

with open(os.path.join(os.path.dirname(__file__), "..", "files", "test-key.gpg.pub.asc")) as f:
    PUB_KEY = f.read()


def test_MetadataSyncJob_success(mocker, homedir, session, session_maker):
    job = MetadataSyncJob(homedir)

    mock_source = factory.RemoteSource(
        key={"type": "PGP", "public": PUB_KEY, "fingerprint": "123456ABC"}
    )

    mock_get_remote_data = mocker.patch(
        "securedrop_client.api_jobs.sync.get_remote_data", return_value=([mock_source], [], [])
    )

    api_client = mocker.MagicMock()
    api_client.default_request_timeout = mocker.MagicMock()
    api_client.default_request_timeout = mocker.MagicMock()

    job.call_api(api_client, session)

    assert mock_get_remote_data.call_count == 1


def test_MetadataSyncJob_success_with_missing_key(mocker, homedir, session, session_maker):
    """
    Check that we can gracefully handle missing source keys.
    """
    job = MetadataSyncJob(homedir)

    mock_source = factory.RemoteSource(key={"type": "PGP", "public": "", "fingerprint": ""})

    mock_get_remote_data = mocker.patch(
        "securedrop_client.api_jobs.sync.get_remote_data", return_value=([mock_source], [], [])
    )

    api_client = mocker.MagicMock()
    api_client.default_request_timeout = mocker.MagicMock()

    job.call_api(api_client, session)

    assert mock_get_remote_data.call_count == 1
