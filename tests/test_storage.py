"""
Tests for storage sync logic.
"""
import pytest
import uuid
from dateutil.parser import parse
from unittest import mock
from securedrop_client.storage import sync_sources, sync_submissions
from sdclientapi import Source


def make_remote_source():
    """
    Utility function for generating sdclientapi Source instances to act upon
    in the following unit tests.
    """
    return Source(add_star_url='foo', interaction_count=1, is_flagged=False,
                  is_starred=True, journalist_designation='foo', key='bar',
                  last_updated='2018-09-11T11:42:31.366649Z',
                  number_of_documents=1, number_of_messages=1,
                  remove_star_url='baz', replies_url='qux',
                  submissions_url='wibble', url='url',
                  uuid=str(uuid.uuid4()))


def test_sync_sources_handles_api_error():
    """
    Ensure any error encountered when accessing the API is logged but the
    caller handles the exception.
    """
    mock_api = mock.MagicMock()
    mock_api.get_sources.side_effect = Exception('BANG!')
    mock_session = mock.MagicMock()
    with pytest.raises(Exception):
        sync_sources(mock_api, mock_session)


def test_sync_remote_sources():
    """
    Check that:

    * Existing sources are updated in the local database.
    * New sources have an entry in the local database.
    * Local sources not returned by the remote server are deleted from the
      local database.
    """
    # Some source objects from the API, one of which will exist in the local
    # database, the other will NOT exist in the local source database (this
    # will be added to the database)
    mock_api = mock.MagicMock()
    source_to_update = make_remote_source()
    source_to_create = make_remote_source()
    mock_api.get_sources.return_value = [source_to_update, source_to_create]
    # Some local source objects. One already exists in the API results (this
    # will be updated), one does NOT exist in the API results (this will be
    # deleted from the local database).
    mock_session = mock.MagicMock()
    mock_local_source1 = mock.MagicMock()
    mock_local_source1.uuid = source_to_update.uuid
    mock_local_source2 = mock.MagicMock()
    mock_local_source2.uuid = str(uuid.uuid4())
    mock_session.query.return_value = [mock_local_source1, mock_local_source2]
    sync_sources(mock_api, mock_session)
    # Check the expected local source object has been updated with values from
    # the API.
    assert mock_local_source1.journalist_designation == source_to_update.journalist_designation
    assert mock_local_source1.is_flagged == source_to_update.is_flagged
    assert mock_local_source1.public_key == source_to_update.key
    assert mock_local_source1.interaction_count == source_to_update.interaction_count
    assert mock_local_source1.is_starred == source_to_update.is_starred
    assert mock_local_source1.last_updated == parse(source_to_update.last_updated)
    # Check the expected local source object has been created with values from
    # the API.
    assert mock_session.add.call_count == 1
    new_local_session = mock_session.add.call_args_list[0][0][0]
    assert new_local_session.uuid == source_to_create.uuid
    assert new_local_session.journalist_designation == source_to_create.journalist_designation
    assert new_local_session.is_flagged == source_to_create.is_flagged
    assert new_local_session.public_key == source_to_create.key
    assert new_local_session.interaction_count == source_to_create.interaction_count
    assert new_local_session.is_starred == source_to_create.is_starred
    assert new_local_session.last_updated == parse(source_to_create.last_updated)
    # Ensure the record for the local source that is missing from the results
    # of the API is deleted.
    mock_session.delete.assert_called_once_with(mock_local_source2)
    # Session is committed to database.
    assert mock_session.commit.call_count == 1
