import pytest

from securedrop_client.api_jobs.sources import DeleteSourceJob
from tests import factory


def test_delete_source_job(homedir, mocker, session, session_maker):
    '''
    Test DeleteSourceJob construction and operation.
    '''
    source = factory.Source()
    session.add(source)
    session.commit()

    api_client = mocker.MagicMock()
    api_client.delete_source = mocker.MagicMock()

    mock_sdk_source = mocker.Mock()
    mock_source_init = mocker.patch(
        'securedrop_client.logic.sdclientapi.Source',
        return_value=mock_sdk_source
    )

    job = DeleteSourceJob(source.uuid)
    uuid = job.call_api(api_client, session)

    assert uuid == source.uuid
    mock_source_init.assert_called_once_with(uuid=source.uuid)
    api_client.delete_source.assert_called_once_with(mock_sdk_source)


def test_failure_to_delete(homedir, mocker, session, session_maker):
    '''
    Check failure of a DeleteSourceJob, which relies on ApiBase for error handling.
    '''
    source = factory.Source()
    session.add(source)
    session.commit()

    api_client = mocker.MagicMock()
    api_client.delete_source = mocker.MagicMock()
    api_client.delete_source.side_effect = Exception

    job = DeleteSourceJob(source.uuid)
    with pytest.raises(Exception):
        job.call_api(api_client, session)
