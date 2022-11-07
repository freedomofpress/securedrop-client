import pytest
from sdclientapi import RequestTimeoutError, ServerConnectionError

from securedrop_client.api_jobs.updatestar import (
    UpdateStarJob,
    UpdateStarJobError,
    UpdateStarJobTimeoutError,
)
from tests import factory


def test_star_if_unstar(homedir, mocker, session, session_maker):
    """
    Check if we call add_star method if a source is not stared.
    """
    source = factory.Source()
    session.add(source)
    session.commit()

    api_client = mocker.MagicMock()

    api_client.add_star = mocker.MagicMock()

    mock_sdk_source = mocker.Mock()
    mock_source_init = mocker.patch(
        "securedrop_client.logic.sdclientapi.Source", return_value=mock_sdk_source
    )

    job = UpdateStarJob(source.uuid, source.is_starred)

    job.call_api(api_client, session)

    # ensure we call add_star with right uuid for source
    mock_source_init.assert_called_once_with(uuid=source.uuid)
    api_client.add_star.assert_called_once_with(mock_sdk_source)


def test_unstar_if_star(homedir, mocker, session, session_maker):
    """
    Check if we call remove_star method if a source is stared.
    """
    source = factory.Source()
    source.is_starred = True
    session.add(source)
    session.commit()

    api_client = mocker.MagicMock()

    api_client.remove_star = mocker.MagicMock()

    mock_sdk_source = mocker.Mock()
    mock_source_init = mocker.patch(
        "securedrop_client.logic.sdclientapi.Source", return_value=mock_sdk_source
    )

    job = UpdateStarJob(source.uuid, source.is_starred)

    job.call_api(api_client, session)

    # ensure we call remove start with right source uuid
    mock_source_init.assert_called_once_with(uuid=source.uuid)
    api_client.remove_star.assert_called_once_with(mock_sdk_source)


def test_call_api_raises_UpdateStarJobError(homedir, mocker, session, session_maker):
    """
    Check that UpdateStarJobError is raised if remove_star fails due to an exception.
    """
    source = factory.Source()
    source.is_starred = True
    session.add(source)
    session.commit()

    api_client = mocker.MagicMock()

    api_client.remove_star = mocker.MagicMock()
    api_client.remove_star.side_effect = Exception

    job = UpdateStarJob(source.uuid, source.is_starred)

    with pytest.raises(UpdateStarJobError):
        job.call_api(api_client, session)


@pytest.mark.parametrize("exception", [RequestTimeoutError, ServerConnectionError])
def test_call_api_raises_UpdateStarJobTimeoutError(mocker, session, exception):
    """
    Check that UpdateStarJobTimeoutError is raised if remove_star fails due to a timeout.
    """
    source = factory.Source()
    source.is_starred = True
    session.add(source)
    session.commit()

    api_client = mocker.MagicMock()
    api_client.remove_star = mocker.MagicMock()
    api_client.remove_star.side_effect = exception()

    job = UpdateStarJob(source.uuid, source.is_starred)

    error = f"Failed to update star on source {source.uuid} due to error"
    with pytest.raises(UpdateStarJobTimeoutError, match=error):
        job.call_api(api_client, session)
