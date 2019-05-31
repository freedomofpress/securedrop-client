"""
Tests for storage sync logic.
"""
import pytest
import os
import uuid
from dateutil.parser import parse

from sqlalchemy.orm.exc import NoResultFound

import securedrop_client.db
from securedrop_client.storage import get_local_sources, get_local_messages, get_local_replies, \
    get_remote_data, update_local_storage, update_sources, update_files, update_messages, \
    update_replies, find_or_create_user, find_new_messages, find_new_replies, add_reply, \
    mark_file_as_downloaded, mark_reply_as_downloaded, delete_single_submission_or_reply_on_disk, \
    rename_file, get_local_files, find_new_files, mark_message_as_downloaded, \
    set_object_decryption_status_with_content
from securedrop_client import db
from sdclientapi import Source, Submission, Reply

from tests import factory


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
    return Submission(download_url='test', filename='1-submission.filename',
                      is_read=False, size=123, source_url=source_url,
                      submission_url='test', uuid=str(uuid.uuid4()))


def make_remote_reply(source_uuid, journalist_uuid='testymctestface'):
    """
    Utility function for generating sdclientapi Reply instances to act
    upon in the following unit tests. The passed in source_uuid is used to
    generate a valid URL.
    """
    source_url = '/api/v1/sources/{}'.format(source_uuid)
    return Reply(filename='1-reply.filename', journalist_uuid=journalist_uuid,
                 journalist_username='test',
                 is_deleted_by_source=False, reply_url='test', size=1234,
                 source_url=source_url, uuid=str(uuid.uuid4()))


def test_get_local_sources(mocker):
    """
    At this moment, just return all sources.
    """
    mock_session = mocker.MagicMock()
    get_local_sources(mock_session)
    mock_session.query.assert_called_once_with(securedrop_client.db.Source)


def test_get_local_messages(mocker):
    """
    At this moment, just return all messages.
    """
    mock_session = mocker.MagicMock()
    get_local_messages(mock_session)
    mock_session.query.\
        assert_called_once_with(securedrop_client.db.Message)


def test_get_local_files(mocker):
    """
    At this moment, just return all files (submissions)
    """
    mock_session = mocker.MagicMock()
    get_local_files(mock_session)
    mock_session.query.\
        assert_called_once_with(securedrop_client.db.File)


def test_get_local_replies(mocker):
    """
    At this moment, just return all replies.
    """
    mock_session = mocker.MagicMock()
    get_local_replies(mock_session)
    mock_session.query.assert_called_once_with(securedrop_client.db.Reply)


def test_get_remote_data_handles_api_error(mocker):
    """
    Ensure any error encountered when accessing the API is logged but the
    caller handles the exception.
    """
    mock_api = mocker.MagicMock()
    mock_api.get_sources.side_effect = Exception('BANG!')
    with pytest.raises(Exception):
        get_remote_data(mock_api)


def test_get_remote_data(mocker):
    """
    In the good case, a tuple of results is returned.
    """
    # Some source, submission and reply objects from the API.
    mock_api = mocker.MagicMock()
    source = make_remote_source()
    mock_api.get_sources.return_value = [source, ]
    submission = mocker.MagicMock()
    mock_api.get_submissions.return_value = [submission, ]
    reply = mocker.MagicMock()
    mock_api.get_all_replies.return_value = [reply, ]
    sources, submissions, replies = get_remote_data(mock_api)
    assert sources == [source, ]
    assert submissions == [submission, ]
    assert replies == [reply, ]


def test_update_local_storage(homedir, mocker):
    """
    Assuming no errors getting data, check the expected functions to update
    the state of the local database are called with the necessary data.
    """
    remote_source = make_remote_source()
    remote_message = mocker.Mock(filename='1-foo.msg.gpg')
    remote_file = mocker.Mock(filename='2-foo.gpg')
    remote_submissions = [remote_message, remote_file]
    remote_reply = mocker.MagicMock()
    # Some local source, submission and reply objects from the local database.
    mock_session = mocker.MagicMock()
    local_source = mocker.MagicMock()
    local_file = mocker.MagicMock()
    local_message = mocker.MagicMock()
    local_reply = mocker.MagicMock()
    mock_session.query().all = mocker.Mock()
    mock_session.query().all.side_effect = [
        [local_source], [local_file], [local_message], [local_reply]]
    src_fn = mocker.patch('securedrop_client.storage.update_sources')
    rpl_fn = mocker.patch('securedrop_client.storage.update_replies')
    file_fn = mocker.patch('securedrop_client.storage.update_files')
    msg_fn = mocker.patch('securedrop_client.storage.update_messages')

    update_local_storage(mock_session, [remote_source], remote_submissions, [remote_reply], homedir)
    src_fn.assert_called_once_with([remote_source], [local_source], mock_session, homedir)
    rpl_fn.assert_called_once_with([remote_reply], [local_reply], mock_session, homedir)
    file_fn.assert_called_once_with([remote_file], [local_file], mock_session, homedir)
    msg_fn.assert_called_once_with([remote_message], [local_message], mock_session, homedir)


def test_add_reply(mocker, SessionFactory, homedir):
    # check that reply is to the DB
    mocker.patch('securedrop_client.db.Session', return_value=SessionFactory)
    mock_id = str(uuid.uuid4())
    source = factory.Source()

    add_reply(mock_id, source.uuid, mock_id, '1-spotted-potato-msg.gpg')

    replies = SessionFactory().query(db.Reply).all()
    assert len(replies) == 1


def test_update_sources(homedir, mocker):
    """
    Check that:

    * Existing sources are updated in the local database.
    * New sources have an entry in the local database.
    * Local sources not returned by the remote server are deleted from the
      local database.
    """
    mock_session = mocker.MagicMock()
    # Some source objects from the API, one of which will exist in the local
    # database, the other will NOT exist in the local source database (this
    # will be added to the database)
    source_update = make_remote_source()
    source_create = make_remote_source()
    remote_sources = [source_update, source_create]
    # Some local source objects. One already exists in the API results (this
    # will be updated), one does NOT exist in the API results (this will be
    # deleted from the local database).
    local_source1 = mocker.MagicMock()
    local_source1.uuid = source_update.uuid
    local_source2 = mocker.MagicMock()
    local_source2.uuid = str(uuid.uuid4())
    local_sources = [local_source1, local_source2]
    update_sources(remote_sources, local_sources, mock_session, homedir)
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


def test_update_files_renames_file_on_disk(homedir, mocker):
    """
    Check that:

    * Submissions are renamed on disk after sync.
    """
    data_dir = os.path.join(homedir, 'data')
    mock_session = mocker.MagicMock()
    # Remote submission with new filename
    server_filename = '1-spotted-potato-msg.gpg'
    remote_submission = mocker.MagicMock()
    remote_submission.uuid = 'test-uuid'
    remote_submission.filename = server_filename
    remote_submissions = [remote_submission]
    # Local submission that needs to be updated
    local_filename = '1-pericardial-surfacing-msg.gpg'
    local_submission = mocker.MagicMock()
    local_submission.uuid = 'test-uuid'
    local_submission.filename = local_filename
    local_submissions = [local_submission]
    # Add submission file to test directory
    local_filename_decrypted = '1-pericardial-surfacing-msg'
    add_test_file_to_temp_dir(data_dir, local_filename_decrypted)
    # There needs to be a corresponding local_source.
    local_source = mocker.MagicMock()
    local_source.uuid = 'test-source-uuid'
    local_source.id = 123
    mock_session.query().filter_by.return_value = [local_source, ]

    update_files(remote_submissions, local_submissions, mock_session, data_dir)

    updated_local_filename = '1-spotted-potato-msg'
    assert local_submission.filename == remote_submission.filename
    assert os.path.exists(os.path.join(data_dir, updated_local_filename))


def test_update_replies_renames_file_on_disk(homedir, mocker):
    """
    Check that:

    * Replies are renamed on disk after sync.
    """
    data_dir = os.path.join(homedir, 'data')
    mock_session = mocker.MagicMock()
    # Remote replies with new filename
    server_filename = '1-spotted-potato-reply.gpg'
    remote_reply = mocker.MagicMock()
    remote_reply.uuid = 'test-uuid'
    remote_reply.filename = server_filename
    remote_replies = [remote_reply]
    # Local reply that needs to be updated
    local_filename = '1-pericardial-surfacing-reply.gpg'
    local_reply = mocker.MagicMock()
    local_reply.uuid = 'test-uuid'
    local_reply.filename = local_filename
    local_replies = [local_reply]
    # Add reply file to test directory
    local_filename_decrypted = '1-pericardial-surfacing-reply'
    add_test_file_to_temp_dir(data_dir, local_filename_decrypted)
    # There needs to be a corresponding local_source and local_user
    local_source = mocker.MagicMock()
    local_source.uuid = 'test-source-uuid'
    local_source.id = 123
    local_user = mocker.MagicMock()
    local_user.username = 'jounalist designation'
    local_user.id = 42
    mock_focu = mocker.MagicMock(return_value=local_user)
    mocker.patch('securedrop_client.storage.find_or_create_user', mock_focu)

    update_replies(remote_replies, local_replies, mock_session, data_dir)

    updated_local_filename = '1-spotted-potato-reply'
    assert local_reply.filename == remote_reply.filename
    assert os.path.exists(os.path.join(data_dir, updated_local_filename))


def add_test_file_to_temp_dir(home_dir, filename):
    """
    Add test file with the given filename to data dir.
    """

    dest = os.path.join(home_dir, filename)
    with open(dest, 'w') as f:
        f.write('I am test content for tests')

    return dest


def test_update_submissions_deletes_files_associated_with_the_submission(
        homedir,
        mocker):
    """
    Check that:

    * Submissions are deleted on disk after sync.
    """
    mock_session = mocker.MagicMock()

    # Test scenario: one submission locally, no submissions on server.
    remote_submissions = []

    # A local submission object. To ensure that all files from various
    # stages of processing are cleaned up, we'll add several filenames.
    server_filename = '1-pericardial-surfacing-msg.gpg'
    local_filename_when_decrypted = '1-pericardial-surfacing-msg'

    local_submission = mocker.MagicMock()
    local_submission.uuid = 'test-uuid'
    local_submission.filename = server_filename
    abs_server_filename = add_test_file_to_temp_dir(
        homedir, server_filename)
    abs_local_filename = add_test_file_to_temp_dir(
        homedir, local_filename_when_decrypted)
    local_submissions = [local_submission]

    # There needs to be a corresponding local_source.
    local_source = mocker.MagicMock()
    local_source.uuid = 'test-source-uuid'
    local_source.id = 666
    mock_session.query().filter_by.return_value = [local_source, ]
    update_files(remote_submissions, local_submissions, mock_session, homedir)

    # Ensure the files associated with the submission are deleted on disk.
    assert not os.path.exists(abs_server_filename)
    assert not os.path.exists(abs_local_filename)

    # Ensure the record for the local submission is gone.
    mock_session.delete.assert_called_once_with(local_submission)

    # Session is committed to database.
    assert mock_session.commit.call_count == 1


def test_update_replies_deletes_files_associated_with_the_reply(
        homedir,
        mocker):
    """
    Check that:

    * Replies are deleted on disk after sync.
    """
    mock_session = mocker.MagicMock()

    # Test scenario: one reply locally, no replies on server.
    remote_replies = []

    # A local reply object. To ensure that all files from various
    # stages of processing are cleaned up, we'll add several filenames.
    server_filename = '1-pericardial-surfacing-reply.gpg'
    local_filename_when_decrypted = '1-pericardial-surfacing-reply'

    local_reply = mocker.MagicMock()
    local_reply.uuid = 'test-uuid'
    local_reply.filename = server_filename
    abs_server_filename = add_test_file_to_temp_dir(
        homedir, server_filename)
    abs_local_filename = add_test_file_to_temp_dir(
        homedir, local_filename_when_decrypted)
    local_replies = [local_reply]

    # There needs to be a corresponding local_source.
    local_source = mocker.MagicMock()
    local_source.uuid = 'test-source-uuid'
    local_source.id = 666
    mock_session.query().filter_by.return_value = [local_source, ]
    update_replies(remote_replies, local_replies, mock_session, homedir)

    # Ensure the files associated with the reply are deleted on disk.
    assert not os.path.exists(abs_server_filename)
    assert not os.path.exists(abs_local_filename)

    # Ensure the record for the local reply is gone.
    mock_session.delete.assert_called_once_with(local_reply)

    # Session is committed to database.
    assert mock_session.commit.call_count == 1


def test_update_sources_deletes_files_associated_with_the_source(
        homedir,
        mocker):
    """
    Check that:

    * Sources are deleted on disk after sync.
    """
    mock_session = mocker.MagicMock()

    # Test scenario: one source locally, no sources on server.
    remote_sources = []

    # A local source object. To ensure that all submissions/replies from
    # various stages of processing are cleaned up, we'll add several filenames
    # associated with each message, document, and reply for each stage of processing.
    # This simulates if a step failed.
    msg_server_filename = '1-pericardial-surfacing-msg.gpg'
    msg_local_filename_decrypted = '1-pericardial-surfacing-msg'

    file_server_filename = '1-pericardial-surfacing-doc.gz.gpg'
    file_local_filename_decompressed = '1-pericardial-surfacing-doc'
    file_local_filename_decrypted = '1-pericardial-surfacing-doc.gz'

    reply_server_filename = '1-pericardial-surfacing-reply.gpg'
    reply_local_filename_decrypted = '1-pericardial-surfacing-reply'

    # Here we're not mocking out the models use so that we can use the collection attribute.
    local_source = factory.Source()
    file_submission = db.File(
        source=local_source, uuid="test", size=123, filename=file_server_filename,
        download_url='http://test/test')
    msg_submission = db.File(
        source=local_source, uuid="test", size=123, filename=msg_server_filename,
        download_url='http://test/test')
    user = db.User(username='hehe')
    reply = db.Reply(
        source=local_source, journalist=user, filename=reply_server_filename,
        size=1234, uuid='test')
    local_source.submissions = [file_submission, msg_submission]
    local_source.replies = [reply]

    # Make the test files on disk in tmpdir so we can check they get deleted.
    test_filename_absolute_paths = []
    for test_filename in [msg_server_filename, msg_local_filename_decrypted,
                          file_server_filename, file_local_filename_decompressed,
                          file_local_filename_decrypted, reply_server_filename,
                          reply_local_filename_decrypted]:
        abs_server_filename = add_test_file_to_temp_dir(
            homedir, test_filename)
        test_filename_absolute_paths.append(abs_server_filename)

    local_sources = [local_source]
    update_sources(remote_sources, local_sources, mock_session, homedir)

    # Ensure the files associated with the reply are deleted on disk.
    for test_filename in test_filename_absolute_paths:
        assert not os.path.exists(test_filename)

    # Ensure the record for the local source is gone, along with its
    # related files.
    mock_session.delete.assert_called_with(local_source)

    # Session is committed to database.
    assert mock_session.commit.call_count == 1


def test_update_files(homedir, mocker):
    """
    Check that:

    * Existing submissions are updated in the local database.
    * New submissions have an entry in the local database.
    * Local submission not returned by the remote server are deleted from the
      local database.
    * `rename_file` is called if local data files need to be updated with new
      filenames to match remote. Note: The only reason this should happen is if
      there is a new journalist_designation that causes remote filenames to be
      updated.
    """
    data_dir = os.path.join(homedir, 'data')
    mock_session = mocker.MagicMock()
    # Source object related to the submissions.
    source = mocker.MagicMock()
    source.uuid = str(uuid.uuid4())
    # Some submission objects from the API, one of which will exist in the
    # local database, the other will NOT exist in the local source database
    # (this will be added to the database)
    remote_sub_update = make_remote_submission(source.uuid)
    remote_sub_create = make_remote_submission(source.uuid)
    remote_submissions = [remote_sub_update, remote_sub_create]
    # Some local submission objects. One already exists in the API results
    # (this will be updated), one does NOT exist in the API results (this will
    # be deleted from the local database).
    local_sub_update = mocker.MagicMock()
    local_sub_update.uuid = remote_sub_update.uuid
    local_sub_update.filename = "overwrite_this.filename"
    local_sub_delete = mocker.MagicMock()
    local_sub_delete.uuid = str(uuid.uuid4())
    local_sub_delete.filename = "local_sub_delete.filename"
    local_submissions = [local_sub_update, local_sub_delete]
    # There needs to be a corresponding local_source.
    local_source = mocker.MagicMock()
    local_source.uuid = source.uuid
    local_source.id = 666  # };-)
    mock_session.query().filter_by.return_value = [local_source, ]
    patch_rename_file = mocker.patch('securedrop_client.storage.rename_file')

    update_files(remote_submissions, local_submissions, mock_session, data_dir)

    # Check the expected local submission object has been updated with values
    # from the API.
    assert local_sub_update.filename == remote_sub_update.filename
    assert local_sub_update.size == remote_sub_update.size
    assert local_sub_update.is_read == remote_sub_update.is_read
    # Check that rename_file is called if the local storage filenames need to
    # be updated
    assert patch_rename_file.called
    # Check the expected local source object has been created with values from
    # the API.
    assert mock_session.add.call_count == 1
    new_sub = mock_session.add.call_args_list[0][0][0]
    assert new_sub.uuid == remote_sub_create.uuid
    assert new_sub.source_id == local_source.id
    assert new_sub.filename == remote_sub_create.filename
    # Ensure the record for the local source that is missing from the results
    # of the API is deleted.
    mock_session.delete.assert_called_once_with(local_sub_delete)
    # Session is committed to database.
    assert mock_session.commit.call_count == 1


def test_update_messages(homedir, mocker):
    """
    Check that:

    * Existing messages are updated in the local database.
    * New messages have an entry in the local database.
    * Local messages not returned by the remote server are deleted from the
      local database.
    * `rename_file` is called if local data files need to be updated with new
      filenames to match remote. Note: The only reason this should happen is if
      there is a new journalist_designation that causes remote filenames to be
      updated.
    """
    data_dir = os.path.join(homedir, 'data')
    mock_session = mocker.MagicMock()
    # Source object related to the submissions.
    source = mocker.MagicMock()
    source.uuid = str(uuid.uuid4())
    # Some remote message objects from the API, one of which will exist in the
    # local database, the other will NOT exist in the local database
    # (this will be added to the database)
    remote_message_update = make_remote_submission(source.uuid)
    remote_message_create = make_remote_submission(source.uuid)
    remote_messages = [remote_message_update, remote_message_create]
    # Some local reply objects. One already exists in the API results
    # (this will be updated), one does NOT exist in the API results (this will
    # be deleted from the local database).
    local_message_update = mocker.MagicMock()
    local_message_update.uuid = remote_message_update.uuid
    local_message_update.filename = "overwrite_this.filename"
    local_message_delete = mocker.MagicMock()
    local_message_delete.uuid = str(uuid.uuid4())
    local_message_delete.filename = "local_message_delete.filename"
    local_messages = [local_message_update, local_message_delete]
    # There needs to be a corresponding local_source and local_user
    local_source = mocker.MagicMock()
    local_source.uuid = source.uuid
    local_source.id = 666  # };-)
    local_user = mocker.MagicMock()
    local_user.id = 42
    mock_session.query().filter_by.side_effect = [[local_source, ],
                                                  [local_user, ],
                                                  [local_user, ], ]
    mock_focu = mocker.MagicMock(return_value=local_user)
    mocker.patch('securedrop_client.storage.find_or_create_user', mock_focu)
    patch_rename_file = mocker.patch('securedrop_client.storage.rename_file')

    update_messages(remote_messages, local_messages, mock_session, data_dir)

    # Check the expected local message object has been updated with values
    # from the API.
    assert local_message_update.filename == remote_message_update.filename
    assert local_message_update.size == remote_message_update.size
    # Check that rename_file is called if the local storage filenames need to
    # be updated
    assert patch_rename_file.called
    # Check the expected local source object has been created with values from
    # the API.
    assert mock_session.add.call_count == 1
    new_reply = mock_session.add.call_args_list[0][0][0]
    assert new_reply.uuid == remote_message_create.uuid
    assert new_reply.source_id == local_source.id
    assert new_reply.size == remote_message_create.size
    assert new_reply.filename == remote_message_create.filename
    # Ensure the record for the local source that is missing from the results
    # of the API is deleted.
    mock_session.delete.assert_called_once_with(local_message_delete)
    # Session is committed to database.
    assert mock_session.commit.call_count == 1


def test_update_replies(homedir, mocker):
    """
    Check that:

    * Existing replies are updated in the local database.
    * New replies have an entry in the local database.
    * Local replies not returned by the remote server are deleted from the
      local database.
    * References to journalist's usernames are correctly handled.
    * `rename_file` is called if local data files need to be updated with new
      filenames to match remote. Note: The only reason this should happen is if
      there is a new journalist_designation that causes remote filenames to be
      updated.
    """
    data_dir = os.path.join(homedir, 'data')
    mock_session = mocker.MagicMock()
    # Source object related to the submissions.
    source = mocker.MagicMock()
    source.uuid = str(uuid.uuid4())
    # Some remote reply objects from the API, one of which will exist in the
    # local database, the other will NOT exist in the local database
    # (this will be added to the database)
    remote_reply_update = make_remote_reply(source.uuid)
    remote_reply_create = make_remote_reply(source.uuid, 'unknownuser')
    remote_replies = [remote_reply_update, remote_reply_create]
    # Some local reply objects. One already exists in the API results
    # (this will be updated), one does NOT exist in the API results (this will
    # be deleted from the local database).
    local_reply_update = mocker.MagicMock()
    local_reply_update.uuid = remote_reply_update.uuid
    local_reply_update.filename = "overwrite_this.filename"
    local_reply_update.journalist_uuid = str(uuid.uuid4())
    local_reply_delete = mocker.MagicMock()
    local_reply_delete.uuid = str(uuid.uuid4())
    local_reply_delete.filename = "local_reply_delete.filename"
    local_reply_delete.journalist_uuid = str(uuid.uuid4())
    local_replies = [local_reply_update, local_reply_delete]
    # There needs to be a corresponding local_source and local_user
    local_source = mocker.MagicMock()
    local_source.uuid = source.uuid
    local_source.id = 666  # };-)
    local_user = mocker.MagicMock()
    local_user.username = remote_reply_create.journalist_username
    local_user.id = 42
    mock_session.query().filter_by.side_effect = [[local_source, ],
                                                  [local_user, ],
                                                  [local_user, ], ]
    mock_focu = mocker.MagicMock(return_value=local_user)
    mocker.patch('securedrop_client.storage.find_or_create_user', mock_focu)
    patch_rename_file = mocker.patch('securedrop_client.storage.rename_file')

    update_replies(remote_replies, local_replies, mock_session, data_dir)

    # Check the expected local reply object has been updated with values
    # from the API.
    assert local_reply_update.journalist_id == local_user.id
    assert local_reply_update.filename == remote_reply_update.filename
    assert local_reply_update.size == remote_reply_update.size
    # Check that rename_file is called if the local storage filenames need to
    # be updated
    assert patch_rename_file.called
    # Check the expected local source object has been created with values from
    # the API.
    assert mock_session.add.call_count == 1
    new_reply = mock_session.add.call_args_list[0][0][0]
    assert new_reply.uuid == remote_reply_create.uuid
    assert new_reply.source_id == local_source.id
    assert new_reply.journalist_id == local_user.id
    assert new_reply.size == remote_reply_create.size
    assert new_reply.filename == remote_reply_create.filename
    # Ensure the record for the local source that is missing from the results
    # of the API is deleted.
    mock_session.delete.assert_called_once_with(local_reply_delete)
    # Session is committed to database.
    assert mock_session.commit.call_count == 1


def test_find_or_create_user_existing_uuid(mocker):
    """
    Return an existing user object with the referenced uuid.
    """
    mock_session = mocker.MagicMock()
    mock_user = mocker.MagicMock()
    mock_user.username = 'foobar'
    mock_session.query().filter_by().one_or_none.return_value = mock_user
    assert find_or_create_user('uuid', 'foobar',
                               mock_session) == mock_user


def test_find_or_create_user_existing_username(mocker):
    """
    Return an existing user object with the referenced username.
    """
    mock_session = mocker.MagicMock()
    mock_user = mocker.MagicMock()
    mock_user.username = 'foobar'
    mock_session.query().filter_by().one_or_none.return_value = mock_user
    assert find_or_create_user('uuid', 'testymctestface',
                               mock_session) == mock_user
    assert mock_user.username == 'testymctestface'
    mock_session.add.assert_called_once_with(mock_user)
    mock_session.commit.assert_called_once_with()


def test_find_or_create_user_new(mocker):
    """
    Create and return a user object for an unknown username.
    """
    mock_session = mocker.MagicMock()
    mock_session.query().filter_by().one_or_none.return_value = None
    new_user = find_or_create_user('uuid', 'unknown', mock_session)
    assert new_user.username == 'unknown'
    mock_session.add.assert_called_once_with(new_user)
    mock_session.commit.assert_called_once_with()


def test_find_new_messages(mocker, session):
    source = factory.Source()
    message_not_downloaded = factory.Message(
        source=source,
        is_downloaded=False,
        is_decrypted=None,
        content=None)
    message_decrypt_not_attempted = factory.Message(
        source=source,
        is_downloaded=True,
        is_decrypted=None,
        content=None)
    message_decrypt_failed = factory.Message(
        source=source,
        is_downloaded=True,
        is_decrypted=False,
        content=None)
    message_decrypt_success = factory.Message(
        source=source,
        is_downloaded=True,
        is_decrypted=True,
        content='teehee')
    session.add(source)
    session.add(message_decrypt_not_attempted)
    session.add(message_not_downloaded)
    session.add(message_decrypt_failed)
    session.add(message_decrypt_success)
    session.commit()

    messages = find_new_messages(session)
    assert len(messages) == 3

    for message in messages:
        assert message.is_downloaded is False or message.is_decrypted is not True


def test_find_new_files(mocker, session):
    mock_session = mocker.MagicMock()
    mock_submission = mocker.MagicMock()
    mock_submission.is_downloaded = False
    mock_submissions = [mock_submission]
    mock_session.query().filter_by().all.return_value = mock_submissions
    submissions = find_new_files(mock_session)
    assert submissions[0].is_downloaded is False


def test_find_new_replies(mocker, session):
    source = factory.Source()
    reply_not_downloaded = factory.Reply(
        source=source,
        is_downloaded=False,
        is_decrypted=None,
        content=None)
    reply_decrypt_not_attempted = factory.Reply(
        source=source,
        is_downloaded=True,
        is_decrypted=None,
        content=None)
    reply_decrypt_failed = factory.Reply(
        source=source,
        is_downloaded=True,
        is_decrypted=False,
        content=None)
    reply_decrypt_success = factory.Reply(
        source=source,
        is_downloaded=True,
        is_decrypted=True,
        content='teehee')
    session.add(source)
    session.add(reply_decrypt_not_attempted)
    session.add(reply_not_downloaded)
    session.add(reply_decrypt_failed)
    session.add(reply_decrypt_success)
    session.commit()

    replies = find_new_replies(session)
    assert len(replies) == 3

    for reply in replies:
        assert reply.is_downloaded is False or reply.is_decrypted is not True


def test_set_object_decryption_status_with_content_null_to_false(mocker, source):
    mock_session = mocker.MagicMock()
    mock_file = mocker.MagicMock()
    mock_file.is_decrypted is None
    mock_session.query().filter_by().one_or_none.return_value = mock_file

    decryption_status = False
    set_object_decryption_status_with_content(mock_file, mock_session, decryption_status)

    assert mock_file.is_decrypted is False

    mock_session.add.assert_called_once_with(mock_file)
    mock_session.commit.assert_called_once_with()


def test_set_object_decryption_status_with_content_false_to_true(mocker):
    mock_session = mocker.MagicMock()
    mock_file = mocker.MagicMock()
    mock_file.is_decrypted is False
    mock_session.query().filter_by().one_or_none.return_value = mock_file

    decryption_status = True
    set_object_decryption_status_with_content(mock_file, mock_session, decryption_status)

    assert mock_file.is_decrypted is True

    mock_session.add.assert_called_once_with(mock_file)
    mock_session.commit.assert_called_once_with()


def test_set_object_decryption_status_with_content_with_content(session, source):
    '''
    It should be possible to set the decryption status of an object in the database to `True`.
    Additionally, if `content` is passed in, the `content` column of the DB should take that
    value. This is to ensure that we have a way to decrypt something without violating the
    condition: if is_decrypted then content is not none.
    '''
    message = factory.Message(source=source['source'],
                              is_downloaded=True,
                              is_decrypted=None,
                              content=None)
    session.add(message)
    session.commit()

    content = 'test'
    set_object_decryption_status_with_content(message, session, True, content)

    # requery to ensure new object
    message = session.query(db.Message).get(message.id)
    assert message.is_decrypted is True
    assert message.content == content


def test_mark_file_as_downloaded(mocker):
    mock_session = mocker.MagicMock()
    mock_submission = mocker.MagicMock()
    mock_submission.is_downloaded is False
    mock_session.query().filter_by().one.return_value = mock_submission
    mark_file_as_downloaded('test-filename', mock_session)
    assert mock_submission.is_downloaded is True
    mock_session.add.assert_called_once_with(mock_submission)
    mock_session.commit.assert_called_once_with()


def test_mark_message_as_downloaded(mocker):
    mock_session = mocker.MagicMock()
    mock_submission = mocker.MagicMock()
    mock_submission.is_downloaded is False
    mock_session.query().filter_by().one.return_value = mock_submission
    mark_message_as_downloaded('test-messagename', mock_session)
    assert mock_submission.is_downloaded is True
    mock_session.add.assert_called_once_with(mock_submission)
    mock_session.commit.assert_called_once_with()


def test_mark_reply_as_downloaded(mocker):
    mock_session = mocker.MagicMock()
    mock_reply = mocker.MagicMock()
    mock_reply.is_downloaded is False
    mock_session.query().filter_by().one.return_value = mock_reply
    mark_reply_as_downloaded('test-filename', mock_session)
    assert mock_reply.is_downloaded is True
    mock_session.add.assert_called_once_with(mock_reply)
    mock_session.commit.assert_called_once_with()


def test_delete_single_submission_or_reply_race_guard(homedir, mocker):
    """
    This test checks that if there is a file is deleted
    locally through another method, that an unhandled exception
    will not occur in delete_single_submission_or_reply_on_disk
    """

    test_obj = mocker.MagicMock()
    test_obj.filename = '1-dissolved-steak-msg.gpg'
    add_test_file_to_temp_dir(homedir, test_obj.filename)

    mock_remove = mocker.patch('os.remove', side_effect=FileNotFoundError)
    delete_single_submission_or_reply_on_disk(test_obj, homedir)

    mock_remove.call_count == 1


def test_rename_file_does_not_throw(homedir):
    """
    If file cannot be found then OSError is caught and logged.
    """
    original_file = 'foo.txt'
    new_file = 'bar.txt'
    rename_file(os.path.join(homedir, 'data'), original_file, new_file)

    assert not os.path.exists(os.path.join(homedir, 'data', original_file))
    assert not os.path.exists(os.path.join(homedir, 'data', new_file))


def test_rename_file_success(homedir):
    """
    If file was renamed successfully then we should be able to retrieve the
    file's content using the new filename.
    """
    data_dir = os.path.join(homedir, 'data')
    orig_filename = 'foo.txt'
    new_filename = 'bar.txt'
    filename, _ = os.path.splitext(orig_filename)
    trunc_new_filename, _ = os.path.splitext(new_filename)
    contents = 'bar'
    with open(os.path.join(data_dir, filename), 'w') as f:
        f.write(contents)

    rename_file(data_dir, orig_filename, new_filename)

    with open(os.path.join(homedir, 'data', trunc_new_filename)) as f:
        out = f.read()
    assert out == contents
