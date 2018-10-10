"""
Tests for storage sync logic.
"""
import pytest
import uuid
import securedrop_client.models
from dateutil.parser import parse
from unittest import mock
from securedrop_client.storage import (get_local_sources,
                                       get_local_submissions,
                                       get_local_replies,
                                       get_remote_data, update_local_storage,
                                       update_sources,
                                       update_submissions, update_replies,
                                       find_or_create_user)
from sdclientapi import Source, Submission, Reply


def make_remote_source():
    """
    Utility function for generating sdclientapi Source instances to act upon
    in the following unit tests.
    """
    return Source(add_star_url='foo', interaction_count=1, is_flagged=False,
                  is_starred=True, journalist_designation='foo',
                  key={'public': 'bar'},
                  last_updated='2018-09-11T11:42:31.366649Z',
                  number_of_documents=1, number_of_messages=1,
                  remove_star_url='baz', replies_url='qux',
                  submissions_url='wibble', url='url',
                  uuid=str(uuid.uuid4()))


def make_remote_submission(source_uuid):
    """
    Utility function for generating sdclientapi Submission instances to act
    upon in the following unit tests. The passed in source_uuid is used to
    generate a valid URL.
    """
    source_url = '/api/v1/sources/{}'.format(source_uuid)
    return Submission(download_url='test', filename='test', is_read=False,
                      size=123, source_url=source_url, submission_url='test',
                      uuid=str(uuid.uuid4()))


def make_remote_reply(source_uuid, journalist_uuid='testymctestface'):
    """
    Utility function for generating sdclientapi Reply instances to act
    upon in the following unit tests. The passed in source_uuid is used to
    generate a valid URL.
    """
    source_url = '/api/v1/sources/{}'.format(source_uuid)
    return Reply(filename='test.filename', journalist_uuid=journalist_uuid,
                 journalist_username='test',
                 is_deleted_by_source=False, reply_url='test', size=1234,
                 source_url=source_url, uuid=str(uuid.uuid4()))


def test_get_local_sources():
    """
    At this moment, just return all sources.
    """
    mock_session = mock.MagicMock()
    get_local_sources(mock_session)
    mock_session.query.assert_called_once_with(securedrop_client.models.Source)


def test_get_local_submissions():
    """
    At this moment, just return all submissions.
    """
    mock_session = mock.MagicMock()
    get_local_submissions(mock_session)
    mock_session.query.\
        assert_called_once_with(securedrop_client.models.Submission)


def test_get_local_replies():
    """
    At this moment, just return all replies.
    """
    mock_session = mock.MagicMock()
    get_local_replies(mock_session)
    mock_session.query.assert_called_once_with(securedrop_client.models.Reply)


def test_get_remote_data_handles_api_error():
    """
    Ensure any error encountered when accessing the API is logged but the
    caller handles the exception.
    """
    mock_api = mock.MagicMock()
    mock_api.get_sources.side_effect = Exception('BANG!')
    mock_session = mock.MagicMock()
    with pytest.raises(Exception):
        get_remote_data(mock_api)


def test_get_remote_data():
    """
    In the good case, a tuple of results is returned.
    """
    # Some source, submission and reply objects from the API.
    mock_api = mock.MagicMock()
    source = make_remote_source()
    mock_api.get_sources.return_value = [source, ]
    submission = mock.MagicMock()
    mock_api.get_submissions.return_value = [submission, ]
    reply = mock.MagicMock()
    mock_api.get_all_replies.return_value = [reply, ]
    sources, submissions, replies = get_remote_data(mock_api)
    assert sources == [source, ]
    assert submissions == [submission, ]
    assert replies == [reply, ]


def test_update_local_storage():
    """
    Assuming no errors getting data, check the expected functions to update
    the state of the local database are called with the necessary data.
    """
    source = make_remote_source()
    submission = mock.MagicMock()
    reply = mock.MagicMock()
    sources = [source, ]
    submissions = [submission, ]
    replies = [reply, ]
    # Some local source, submission and reply objects from the local database.
    mock_session = mock.MagicMock()
    local_source = mock.MagicMock()
    local_submission = mock.MagicMock()
    local_replies = mock.MagicMock()
    mock_session.query.side_effect = [[local_source, ], [local_submission, ],
                                      [local_replies, ], ]
    with mock.patch('securedrop_client.storage.update_sources') as src_fn, \
            mock.patch('securedrop_client.storage.update_replies') as rpl_fn, \
            mock.patch('securedrop_client.storage.update_submissions') \
            as sub_fn:
        update_local_storage(mock_session, sources, submissions, replies)
        src_fn.assert_called_once_with([source, ], [local_source, ],
                                       mock_session)
        rpl_fn.assert_called_once_with([reply, ], [local_replies, ],
                                       mock_session)
        sub_fn.assert_called_once_with([submission, ], [local_submission, ],
                                       mock_session)


def test_update_sources():
    """
    Check that:

    * Existing sources are updated in the local database.
    * New sources have an entry in the local database.
    * Local sources not returned by the remote server are deleted from the
      local database.
    """
    mock_session = mock.MagicMock()
    # Some source objects from the API, one of which will exist in the local
    # database, the other will NOT exist in the local source database (this
    # will be added to the database)
    source_update = make_remote_source()
    source_create = make_remote_source()
    remote_sources = [source_update, source_create]
    # Some local source objects. One already exists in the API results (this
    # will be updated), one does NOT exist in the API results (this will be
    # deleted from the local database).
    local_source1 = mock.MagicMock()
    local_source1.uuid = source_update.uuid
    local_source2 = mock.MagicMock()
    local_source2.uuid = str(uuid.uuid4())
    local_sources = [local_source1, local_source2]
    update_sources(remote_sources, local_sources, mock_session)
    # Check the expected local source object has been updated with values from
    # the API.
    assert local_source1.journalist_designation == \
        source_update.journalist_designation
    assert local_source1.is_flagged == source_update.is_flagged
    assert local_source1.public_key == source_update.key['public']
    assert local_source1.interaction_count == source_update.interaction_count
    assert local_source1.is_starred == source_update.is_starred
    assert local_source1.last_updated == parse(source_update.last_updated)
    # Check the expected local source object has been created with values from
    # the API.
    assert mock_session.add.call_count == 1
    new_source = mock_session.add.call_args_list[0][0][0]
    assert new_source.uuid == source_create.uuid
    assert new_source.journalist_designation == \
        source_create.journalist_designation
    assert new_source.is_flagged == source_create.is_flagged
    assert new_source.public_key == source_create.key['public']
    assert new_source.interaction_count == source_create.interaction_count
    assert new_source.is_starred == source_create.is_starred
    assert new_source.last_updated == parse(source_create.last_updated)
    # Ensure the record for the local source that is missing from the results
    # of the API is deleted.
    mock_session.delete.assert_called_once_with(local_source2)
    # Session is committed to database.
    assert mock_session.commit.call_count == 1


def test_update_submissions():
    """
    Check that:

    * Existing submissions are updated in the local database.
    * New submissions have an entry in the local database.
    * Local submission not returned by the remote server are deleted from the
      local database.
    """
    mock_session = mock.MagicMock()
    # Source object related to the submissions.
    source = mock.MagicMock()
    source.uuid = str(uuid.uuid4())
    # Some submission objects from the API, one of which will exist in the
    # local database, the other will NOT exist in the local source database
    # (this will be added to the database)
    submission_update = make_remote_submission(source.uuid)
    submission_create = make_remote_submission(source.uuid)
    remote_submissions = [submission_update, submission_create]
    # Some local submission objects. One already exists in the API results
    # (this will be updated), one does NOT exist in the API results (this will
    # be deleted from the local database).
    local_sub1 = mock.MagicMock()
    local_sub1.uuid = submission_update.uuid
    local_sub2 = mock.MagicMock()
    local_sub2.uuid = str(uuid.uuid4())
    local_submissions = [local_sub1, local_sub2]
    # There needs to be a corresponding local_source.
    local_source = mock.MagicMock()
    local_source.uuid = source.uuid
    local_source.id = 666  # ;-)
    mock_session.query().filter_by.return_value = [local_source, ]
    update_submissions(remote_submissions, local_submissions, mock_session)
    # Check the expected local submission object has been updated with values
    # from the API.
    assert local_sub1.filename == submission_update.filename
    assert local_sub1.size == submission_update.size
    assert local_sub1.is_read == submission_update.is_read
    # Check the expected local source object has been created with values from
    # the API.
    assert mock_session.add.call_count == 1
    new_sub = mock_session.add.call_args_list[0][0][0]
    assert new_sub.uuid == submission_create.uuid
    assert new_sub.source_id == local_source.id
    assert new_sub.filename == submission_create.filename
    # Ensure the record for the local source that is missing from the results
    # of the API is deleted.
    mock_session.delete.assert_called_once_with(local_sub2)
    # Session is committed to database.
    assert mock_session.commit.call_count == 1


def test_update_replies():
    """
    Check that:

    * Existing replies are updated in the local database.
    * New replies have an entry in the local database.
    * Local replies not returned by the remote server are deleted from the
      local database.
    * References to journalist's usernames are correctly handled.
    """
    mock_session = mock.MagicMock()
    # Source object related to the submissions.
    source = mock.MagicMock()
    source.uuid = str(uuid.uuid4())
    # Some remote reply objects from the API, one of which will exist in the
    # local database, the other will NOT exist in the local database
    # (this will be added to the database)
    reply_update = make_remote_reply(source.uuid)
    reply_create = make_remote_reply(source.uuid, 'unknownuser')
    remote_replies = [reply_update, reply_create]
    # Some local reply objects. One already exists in the API results
    # (this will be updated), one does NOT exist in the API results (this will
    # be deleted from the local database).
    local_reply1 = mock.MagicMock()
    local_reply1.uuid = reply_update.uuid
    local_reply2 = mock.MagicMock()
    local_reply2.uuid = str(uuid.uuid4())
    local_replies = [local_reply1, local_reply2]
    # There needs to be a corresponding local_source and local_user
    local_source = mock.MagicMock()
    local_source.uuid = source.uuid
    local_source.id = 666  # ;-)
    local_user = mock.MagicMock()
    local_user.username = reply_create.journalist_username
    local_user.id = 42
    mock_session.query().filter_by.side_effect = [[local_source, ],
                                                  [local_user, ],
                                                  [local_user, ], ]
    mock_focu = mock.MagicMock(return_value=local_user)
    with mock.patch('securedrop_client.storage.find_or_create_user',
                    mock_focu):
        update_replies(remote_replies, local_replies, mock_session)
    # Check the expected local reply object has been updated with values
    # from the API.
    assert local_reply1.journalist_id == local_user.id
    assert local_reply1.filename == reply_update.filename
    assert local_reply1.size == reply_update.size
    # Check the expected local source object has been created with values from
    # the API.
    assert mock_session.add.call_count == 1
    new_reply = mock_session.add.call_args_list[0][0][0]
    assert new_reply.uuid == reply_create.uuid
    assert new_reply.source_id == local_source.id
    assert new_reply.journalist_id == local_user.id
    assert new_reply.size == reply_create.size
    assert new_reply.filename == reply_create.filename
    # Ensure the record for the local source that is missing from the results
    # of the API is deleted.
    mock_session.delete.assert_called_once_with(local_reply2)
    # Session is committed to database.
    assert mock_session.commit.call_count == 1


def test_find_or_create_user_existing_uuid():
    """
    Return an existing user object with the referenced uuid.
    """
    mock_session = mock.MagicMock()
    mock_user = mock.MagicMock()
    mock_user.username = 'foobar'
    mock_session.query().filter_by().one_or_none.return_value = mock_user
    assert find_or_create_user('uuid', 'foobar',
                               mock_session) == mock_user


def test_find_or_create_user_existing_username():
    """
    Return an existing user object with the referenced username.
    """
    mock_session = mock.MagicMock()
    mock_user = mock.MagicMock()
    mock_user.username = 'foobar'
    mock_session.query().filter_by().one_or_none.return_value = mock_user
    assert find_or_create_user('uuid', 'testymctestface',
                               mock_session) == mock_user
    assert mock_user.username == 'testymctestface'
    mock_session.add.assert_called_once_with(mock_user)
    mock_session.commit.assert_called_once_with()


def test_find_or_create_user_new():
    """
    Create and return a user object for an unknown username.
    """
    mock_session = mock.MagicMock()
    mock_session.query().filter_by().one_or_none.return_value = None
    new_user = find_or_create_user('uuid', 'unknown', mock_session)
    assert new_user.username == 'unknown'
    mock_session.add.assert_called_once_with(new_user)
    mock_session.commit.assert_called_once_with()
