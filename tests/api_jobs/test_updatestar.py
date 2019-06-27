import pytest

from securedrop_client.api_jobs.updatestar import UpdateStarJob, UpdateStarJobException
from tests import factory


def test_star_if_unstar(homedir, mocker, session, session_maker):
    '''
    Check if we call add_star method if a source is not stared.
    '''
    source = factory.Source()
    session.add(source)
    session.commit()

    api_client = mocker.MagicMock()

    api_client.add_star = mocker.MagicMock()

    mock_sdk_source = mocker.Mock()
    mock_source_init = mocker.patch('securedrop_client.logic.sdclientapi.Source',
                                    return_value=mock_sdk_source)

    job = UpdateStarJob(
        source.uuid,
        source.is_starred
    )

    job.call_api(api_client, session)

    # ensure we call add_star with right uuid for source
    mock_source_init.assert_called_once_with(uuid=source.uuid)
    api_client.add_star.assert_called_once_with(mock_sdk_source)


def test_unstar_if_star(homedir, mocker, session, session_maker):
    '''
    Check if we call remove_star method if a source is stared.
    '''
    source = factory.Source()
    source.is_starred = True
    session.add(source)
    session.commit()

    api_client = mocker.MagicMock()

    api_client.remove_star = mocker.MagicMock()

    mock_sdk_source = mocker.Mock()
    mock_source_init = mocker.patch('securedrop_client.logic.sdclientapi.Source',
                                    return_value=mock_sdk_source)

    job = UpdateStarJob(
        source.uuid,
        source.is_starred
    )

    job.call_api(api_client, session)

    # ensure we call remove start wtih right source uuid
    mock_source_init.assert_called_once_with(uuid=source.uuid)
    api_client.remove_star.assert_called_once_with(mock_sdk_source)


def test_failure_to_star(homedir, mocker, session, session_maker):
    '''
    Check if we call remove_star method if a source is stared.
    '''
    source = factory.Source()
    source.is_starred = True
    session.add(source)
    session.commit()

    api_client = mocker.MagicMock()

    api_client.remove_star = mocker.MagicMock()
    api_client.remove_star.side_effect = Exception

    job = UpdateStarJob(
        source.uuid,
        source.is_starred
    )

    with pytest.raises(UpdateStarJobException):
        job.call_api(api_client, session)
