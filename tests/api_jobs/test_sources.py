import pytest
from sdclientapi import RequestTimeoutError, ServerConnectionError

from securedrop_client.api_jobs.sources import DeleteSourceJob, DeleteSourceJobException
from tests import factory


def test_delete_source_job(homedir, mocker, session, session_maker):
    """
    Test DeleteSourceJob construction and operation.
    """
    source = factory.Source()
    session.add(source)
    session.commit()

    api_client = mocker.MagicMock()
    api_client.delete_source = mocker.MagicMock()

    mock_sdk_source = mocker.Mock()
    mock_source_init = mocker.patch(
        "securedrop_client.logic.sdclientapi.Source", return_value=mock_sdk_source
    )

    job = DeleteSourceJob(source.uuid)
    uuid = job.call_api(api_client, session)

    assert uuid == source.uuid
    mock_source_init.assert_called_once_with(uuid=source.uuid)
    api_client.delete_source.assert_called_once_with(mock_sdk_source)


def test_failure_to_delete(homedir, mocker, session, session_maker):
    """
    Check failure of a DeleteSourceJob, which should raise a custom exception.
    """
    source = factory.Source()
    session.add(source)
    session.commit()

    api_client = mocker.MagicMock()
    api_client.delete_source = mocker.MagicMock()
    api_client.delete_source.side_effect = Exception

    job = DeleteSourceJob(source.uuid)
    with pytest.raises(DeleteSourceJobException):
        job.call_api(api_client, session)


@pytest.mark.parametrize("exception", [RequestTimeoutError, ServerConnectionError])
def test_failure_to_delete_timeout(homedir, mocker, session, session_maker, exception):
    """
    Check failure of a DeleteSourceJob due to timeouts, which should raise for ApiBase
    to handle.
    """
    source = factory.Source()
    session.add(source)
    session.commit()

    api_client = mocker.MagicMock()
    api_client.delete_source = mocker.MagicMock()
    api_client.delete_source.side_effect = exception()

    job = DeleteSourceJob(source.uuid)
    with pytest.raises(exception):
        job.call_api(api_client, session)
