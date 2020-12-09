"""
Tests for storage sync logic.
"""
import datetime
import os
import time
import uuid

import pytest
from dateutil.parser import parse
from PyQt5.QtCore import QThread
from sdclientapi import Reply, Submission
from sqlalchemy.orm.exc import NoResultFound

import securedrop_client.db
from securedrop_client import db
from securedrop_client.storage import (
    create_or_update_user,
    delete_local_source_by_uuid,
    delete_single_submission_or_reply_on_disk,
    find_new_files,
    find_new_messages,
    find_new_replies,
    get_file,
    get_local_files,
    get_local_messages,
    get_local_replies,
    get_local_sources,
    get_message,
    get_remote_data,
    get_reply,
    mark_all_pending_drafts_as_failed,
    mark_as_decrypted,
    mark_as_downloaded,
    mark_as_not_downloaded,
    set_message_or_reply_content,
    source_exists,
    update_draft_replies,
    update_file_size,
    update_files,
    update_local_storage,
    update_messages,
    update_missing_files,
    update_replies,
    update_sources,
)
from tests import factory


def make_remote_message(source_uuid, file_counter=1):
    """
    Utility function for generating sdclientapi Message instances to act
    upon in the following unit tests. The passed in source_uuid is used to
    generate a valid URL.
    """
    source_url = "/api/v1/sources/{}".format(source_uuid)
    return Submission(
        download_url="test",
        filename="{}-submission.msg.gpg".format(file_counter),
        is_read=False,
        size=123,
        source_url=source_url,
        submission_url="test",
        uuid=str(uuid.uuid4()),
        seen_by=[],
    )


def make_remote_submission(source_uuid):
    """
    Utility function for generating sdclientapi Submission instances to act
    upon in the following unit tests. The passed in source_uuid is used to
    generate a valid URL.
    """
    source_url = "/api/v1/sources/{}".format(source_uuid)
    return Submission(
        download_url="test",
        filename="1-submission.filename",
        is_read=False,
        size=123,
        source_url=source_url,
        submission_url="test",
        uuid=str(uuid.uuid4()),
        seen_by=[],
    )


def make_remote_reply(source_uuid, journalist_uuid="testymctestface"):
    """
    Utility function for generating sdclientapi Reply instances to act
    upon in the following unit tests. The passed in source_uuid is used to
    generate a valid URL.
    """
    source_url = "/api/v1/sources/{}".format(source_uuid)
    return Reply(
        filename="1-reply.filename",
        journalist_uuid=journalist_uuid,
        journalist_username="test",
        journalist_first_name="test",
        journalist_last_name="test",
        file_counter=1,
        is_deleted_by_source=False,
        reply_url="test",
        size=1234,
        source_url=source_url,
        uuid=str(uuid.uuid4()),
        seen_by=[],
    )


def test_get_local_sources(mocker):
    """
    At this moment, just return all sources.
    """
    mock_session = mocker.MagicMock()
    get_local_sources(mock_session)
    mock_session.query.assert_called_once_with(securedrop_client.db.Source)


def test_delete_local_source_by_uuid(homedir, mocker):
    """
    Delete the referenced source in the session. Ensure that both
    the database object and the corresponding source documents are deleted.
    """
    mock_session = mocker.MagicMock()
    source = factory.RemoteSource()
    source.journalist_filename = "sourcey_mcsource"

    # Make source folder
    source_directory = os.path.join(homedir, source.journalist_filename)
    os.mkdir(source_directory)

    # Make document in source disk to be deleted
    path_to_source_document = os.path.join(source_directory, "teehee")
    with open(path_to_source_document, "w") as f:
        f.write("this is a source document")

    mock_session.query().filter_by().one_or_none.return_value = source
    mock_session.query.reset_mock()
    delete_local_source_by_uuid(mock_session, "uuid", homedir)
    mock_session.query.assert_called_once_with(securedrop_client.db.Source)
    mock_session.query().filter_by.assert_called_once_with(uuid="uuid")
    assert mock_session.query().filter_by().one_or_none.call_count == 1
    mock_session.delete.assert_called_once_with(source)
    mock_session.commit.assert_called_once_with()

    # Ensure both source folder and its containing file are gone.
    with pytest.raises(FileNotFoundError):
        f = open(path_to_source_document, "r")

    with pytest.raises(FileNotFoundError):
        f = open(source_directory, "r")


def test_delete_local_source_by_uuid_no_files(homedir, mocker):
    """
    Delete the referenced source in the session. If there are no files
    corresponding to this source, no exception should be raised.
    """
    mock_session = mocker.MagicMock()
    source = factory.RemoteSource()
    source.journalist_filename = "sourcey_mcsource"
    mock_session.query().filter_by().one_or_none.return_value = source
    mock_session.query.reset_mock()
    delete_local_source_by_uuid(mock_session, "uuid", homedir)
    mock_session.query.assert_called_once_with(securedrop_client.db.Source)
    mock_session.query().filter_by.assert_called_once_with(uuid="uuid")
    assert mock_session.query().filter_by().one_or_none.call_count == 1
    mock_session.delete.assert_called_once_with(source)
    mock_session.commit.assert_called_once_with()


def test_get_local_messages(mocker):
    """
    At this moment, just return all messages.
    """
    mock_session = mocker.MagicMock()
    get_local_messages(mock_session)
    mock_session.query.assert_called_once_with(securedrop_client.db.Message)


def test_get_local_files(mocker):
    """
    At this moment, just return all files (submissions)
    """
    mock_session = mocker.MagicMock()
    get_local_files(mock_session)
    mock_session.query.assert_called_once_with(securedrop_client.db.File)


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
    mock_api.get_sources.side_effect = Exception("BANG!")
    with pytest.raises(Exception):
        get_remote_data(mock_api)


def test_get_remote_data(mocker):
    """
    In the good case, a tuple of results is returned.
    """
    # Some source, submission and reply objects from the API.
    mock_api = mocker.MagicMock()
    source = factory.RemoteSource()
    mock_api.get_sources.return_value = [source]
    submission = mocker.MagicMock()
    mock_api.get_all_submissions.return_value = [submission]
    reply = mocker.MagicMock()
    mock_api.get_all_replies.return_value = [reply]
    sources, submissions, replies = get_remote_data(mock_api)
    assert sources == [source]
    assert submissions == [submission]
    assert replies == [reply]


def test_update_local_storage(homedir, mocker, session_maker):
    """
    Assuming no errors getting data, check the expected functions to update
    the state of the local database are called with the necessary data.
    """
    remote_source = factory.RemoteSource()
    remote_message = mocker.Mock(filename="1-foo.msg.gpg")
    remote_file = mocker.Mock(filename="2-foo.gpg")
    remote_submissions = [remote_message, remote_file]
    remote_reply = mocker.MagicMock()
    # Some local source, submission and reply objects from the local database.
    mock_session = mocker.MagicMock()
    local_source = mocker.MagicMock()
    local_file = mocker.MagicMock()
    local_message = mocker.MagicMock()
    local_reply = mocker.MagicMock()
    mock_session.query().all = mocker.Mock()
    mock_session.query().all.side_effect = [[local_file], [local_message], [local_reply]]
    mock_session.query().order_by().all = mocker.Mock()
    mock_session.query().order_by().all.side_effect = [[local_source]]
    src_fn = mocker.patch("securedrop_client.storage.update_sources")
    rpl_fn = mocker.patch("securedrop_client.storage.update_replies")
    file_fn = mocker.patch("securedrop_client.storage.update_files")
    msg_fn = mocker.patch("securedrop_client.storage.update_messages")

    update_local_storage(mock_session, [remote_source], remote_submissions, [remote_reply], homedir)
    src_fn.assert_called_once_with([remote_source], [local_source], mock_session, homedir)
    rpl_fn.assert_called_once_with([remote_reply], [local_reply], mock_session, homedir)
    file_fn.assert_called_once_with([remote_file], [local_file], mock_session, homedir)
    msg_fn.assert_called_once_with([remote_message], [local_message], mock_session, homedir)


def test_sync_delete_race(homedir, mocker, session_maker, session):
    """
    Test a race between sync and source deletion (#797).

    The original failure scenario:
      0. New source submits message 1.
      1. Sync occurs in client. Journalist sees message 1.
      2. Source submits message 2.
      3. Journalist simultaneously deletes the source while the sync
         begins. Deletion completes as it occurs independently of the
         sync, but by this time the sync has collected the list of new
         messages, which includes message 2.
      4. Source is gone, yet the logic in the sync will attempt to add
         message 2 which corresponds to a source that is deleted.
    """

    source = factory.RemoteSource()
    message1 = make_remote_message(source.uuid)

    sources = [source]
    submissions = [message1]
    replies = []

    update_local_storage(session, sources, submissions, replies, homedir)

    assert source_exists(session, source.uuid)
    get_message(session, message1.uuid)

    message2 = make_remote_message(source.uuid, file_counter=2)
    submissions = [message1, message2]

    class Deleter(QThread):
        def __init__(self, source_uuid):
            super().__init__()
            self.source_uuid = source_uuid

        def run(self):
            session = db.make_session_maker(homedir)()
            session.begin(subtransactions=True)
            delete_local_source_by_uuid(session, self.source_uuid, homedir)
            session.commit()
            self.exit()

    deleter = Deleter(source.uuid)

    def delayed_update_messages(remote_submissions, local_submissions, session, data_dir):
        assert source_exists(session, source.uuid)
        deleter.start()
        time.sleep(1)

        # This next assert should fail if transactions are working, as
        # the source should still be visible in this session -- it's
        # only been deleted in the Deleter's session. If transactions
        # are *not* working, the deletion will be visible here.
        assert source_exists(session, source.uuid) is False
        update_messages(remote_submissions, local_submissions, session, data_dir)

    mocker.patch("securedrop_client.storage.update_messages", delayed_update_messages)

    # simulate update_local_storage being called as part of the sync operation
    update_local_storage(session, sources, [message1, message2], [], homedir)

    assert source_exists(session, source.uuid) is False
    with pytest.raises(NoResultFound):
        get_message(session, message1.uuid)

    assert source_exists(session, source.uuid) is False
    with pytest.raises(NoResultFound):
        get_message(session, message1.uuid)
        get_message(session, message2.uuid)


def test_update_sources(homedir, mocker, session_maker, session):
    """
    Check that:

    * Existing sources are updated in the local database.
    * New sources have an entry in the local database.
    * Local sources not returned by the remote server are deleted from the
      local database.
    """
    # This remote source exists locally and will be updated.
    source_update = factory.RemoteSource(journalist_designation="source update")

    # This remote source does not exist locally and will be created.
    source_create = factory.RemoteSource(journalist_designation="source create")

    remote_sources = [source_update, source_create]

    # This local source already exists in the API results and will be updated.
    local_source1 = factory.Source(
        journalist_designation=source_update.journalist_designation,
        uuid=source_update.uuid,
        public_key=None,
        fingerprint=None,
    )

    # This local source does not exist in the API results and will be
    # deleted from the local database.
    local_source2 = factory.Source(journalist_designation="beep_boop")

    session.add(local_source1)
    session.add(local_source2)
    session.commit()

    local_sources = [local_source1, local_source2]

    file_delete_fcn = mocker.patch("securedrop_client.storage.delete_source_collection")

    update_sources(remote_sources, local_sources, session, homedir)

    # Check the expected local source object has been updated with values from
    # the API.
    updated_source = session.query(db.Source).filter_by(uuid=source_update.uuid).one()
    assert updated_source.journalist_designation == source_update.journalist_designation
    assert updated_source.is_flagged == source_update.is_flagged
    assert updated_source.public_key == source_update.key["public"]
    assert updated_source.fingerprint == source_update.key["fingerprint"]
    assert updated_source.interaction_count == source_update.interaction_count
    assert updated_source.is_starred == source_update.is_starred
    assert updated_source.last_updated == parse(source_update.last_updated)

    # Check the expected local source object has been created with values from
    # the API.
    new_source = session.query(db.Source).filter_by(uuid=source_create.uuid).one()
    assert new_source.uuid == source_create.uuid
    assert new_source.journalist_designation == source_create.journalist_designation
    assert new_source.is_flagged == source_create.is_flagged
    assert new_source.public_key == source_create.key["public"]
    assert new_source.fingerprint == source_create.key["fingerprint"]
    assert new_source.interaction_count == source_create.interaction_count
    assert new_source.is_starred == source_create.is_starred
    assert new_source.last_updated == parse(source_create.last_updated)

    # Check that the local source not present in the API results was deleted.
    with pytest.raises(NoResultFound):
        session.query(db.Source).filter_by(uuid=local_source2.uuid).one()

    # Ensure that we called the method to delete the source collection.
    # This will delete any content in that source's data directory.
    assert file_delete_fcn.call_count == 1


def add_test_file_to_temp_dir(home_dir, filename):
    """
    Add test file with the given filename to data dir.
    """

    dest = os.path.join(home_dir, filename)
    os.makedirs(os.path.dirname(dest), mode=0o700, exist_ok=True)
    with open(dest, "w") as f:
        f.write("I am test content for tests")

    return dest


def test_update_submissions_deletes_files_associated_with_the_submission(homedir, mocker):
    """
    Check that:

    * Submissions are deleted on disk after sync.
    """
    mock_session = mocker.MagicMock()

    # Test scenario: one submission locally, no submissions on server.
    remote_submissions = []

    # A local submission object. To ensure that all files from various
    # stages of processing are cleaned up, we'll add several filenames.
    server_filename = "1-pericardial-surfacing-msg.gpg"
    local_filename_when_decrypted = "1-pericardial-surfacing-msg"

    local_submission = mocker.MagicMock()
    local_submission.uuid = "test-uuid"
    local_submission.filename = server_filename
    local_submission_source_journalist_filename = "pericardial_surfacing"
    source_directory = os.path.join(homedir, local_submission_source_journalist_filename)
    local_submission.location = mocker.MagicMock(
        return_value=os.path.join(source_directory, local_filename_when_decrypted)
    )
    abs_local_filename = add_test_file_to_temp_dir(source_directory, local_filename_when_decrypted)
    local_submissions = [local_submission]

    # There needs to be a corresponding local_source.
    local_source = mocker.MagicMock()
    local_source.uuid = "test-source-uuid"
    local_source.id = 666
    mock_session.query().filter_by.return_value = [local_source]
    update_files(remote_submissions, local_submissions, mock_session, homedir)

    # Ensure the files associated with the submission are deleted on disk.
    assert not os.path.exists(abs_local_filename)

    # Ensure the record for the local submission is gone.
    mock_session.delete.assert_called_once_with(local_submission)

    # Session is committed to database.
    assert mock_session.commit.call_count == 1


def test_update_replies_deletes_files_associated_with_the_reply(homedir, mocker):
    """
    Check that:

    * Replies are deleted on disk after sync.
    """
    mock_session = mocker.MagicMock()

    # Test scenario: one reply locally, no replies on server.
    remote_replies = []

    # A local reply object. To ensure that all files from various
    # stages of processing are cleaned up, we'll add several filenames.
    server_filename = "1-pericardial-surfacing-reply.gpg"
    local_filename_when_decrypted = "1-pericardial-surfacing-reply"

    local_reply = mocker.MagicMock()
    local_reply.uuid = "test-uuid"
    local_reply.filename = server_filename
    local_reply_source_journalist_filename = "pericardial_surfacing"
    source_directory = os.path.join(homedir, local_reply_source_journalist_filename)
    local_reply.location = mocker.MagicMock(
        return_value=os.path.join(source_directory, local_filename_when_decrypted)
    )
    abs_local_filename = add_test_file_to_temp_dir(source_directory, local_filename_when_decrypted)
    local_replies = [local_reply]

    # There needs to be a corresponding local_source.
    local_source = mocker.MagicMock()
    local_source.uuid = "test-source-uuid"
    local_source.id = 666
    mock_session.query().filter_by.return_value = [local_source]
    update_replies(remote_replies, local_replies, mock_session, homedir)

    # Ensure the file associated with the reply are deleted on disk.
    assert not os.path.exists(abs_local_filename)

    # Ensure the record for the local reply is gone.
    mock_session.delete.assert_called_once_with(local_reply)

    # Session is committed to database.
    assert mock_session.commit.call_count == 1


def test_update_sources_deletes_files_associated_with_the_source(homedir, mocker, session_maker):
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
    msg_server_filename = "1-pericardial-surfacing-msg.gpg"
    msg_local_filename_decrypted = "1-pericardial-surfacing-msg"

    file_server_filename = "1-pericardial-surfacing-doc.gz.gpg"
    file_local_filename_decompressed = "1-pericardial-surfacing-doc"
    file_local_filename_decrypted = "1-pericardial-surfacing-doc.gz"

    reply_server_filename = "1-pericardial-surfacing-reply.gpg"
    reply_local_filename_decrypted = "1-pericardial-surfacing-reply"

    # Here we're not mocking out the models use so that we can use the collection attribute.
    local_source = factory.Source(journalist_designation="beep_boop")
    file_submission = db.File(
        source=local_source,
        uuid="test",
        size=123,
        filename=file_server_filename,
        download_url="http://test/test",
    )
    msg_submission = db.File(
        source=local_source,
        uuid="test",
        size=123,
        filename=msg_server_filename,
        download_url="http://test/test",
    )
    user = db.User(username="hehe")
    reply = db.Reply(
        source=local_source, journalist=user, filename=reply_server_filename, size=1234, uuid="test"
    )
    local_source.submissions = [file_submission, msg_submission]
    local_source.replies = [reply]

    # Make the test files on disk in tmpdir so we can check they get deleted.
    test_filename_absolute_paths = []
    sourcedir = os.path.join(homedir, local_source.journalist_filename)
    for test_filename in [
        msg_server_filename,
        msg_local_filename_decrypted,
        file_server_filename,
        file_local_filename_decompressed,
        file_local_filename_decrypted,
        reply_server_filename,
        reply_local_filename_decrypted,
    ]:
        abs_server_filename = add_test_file_to_temp_dir(sourcedir, test_filename)
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
    """
    data_dir = os.path.join(homedir, "data")
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
    local_sub_update.is_downloaded = True
    local_sub_update.is_decrypted = False
    local_filename = "originalsubmissionname.txt"
    local_sub_update.filename = local_filename
    local_sub_delete = mocker.MagicMock()
    local_sub_delete.uuid = str(uuid.uuid4())
    local_sub_delete.filename = "local_sub_delete.filename"
    local_submissions = [local_sub_update, local_sub_delete]
    # There needs to be a corresponding local_source.
    local_source = mocker.MagicMock()
    local_source.uuid = source.uuid
    local_source.id = 666  # };-)
    mock_session.query().filter_by().first.return_value = local_source
    mock_delete_submission_files = mocker.patch(
        "securedrop_client.storage.delete_single_submission_or_reply_on_disk"
    )

    update_files(remote_submissions, local_submissions, mock_session, data_dir)

    # Check the expected local submission object has been updated with values
    # from the API.
    assert local_sub_update.filename == local_filename
    assert local_sub_update.size == remote_sub_update.size
    assert local_sub_update.is_read == remote_sub_update.is_read

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
    mock_delete_submission_files.assert_called_once_with(local_sub_delete, data_dir)
    # Session is committed to database.
    assert mock_session.commit.call_count == 1


def test_update_files_adds_seen_record(homedir, mocker, session):
    """
    Check that:

    * A seen record is created for each journalist in the seen_by field for an existing file.
    * A seen record is created for each journalist in the seen_by field for a new file.
    * Seen records for a deleted file are also deleted.
    * No seen record is created for a journalist without an account.
    """
    data_dir = os.path.join(homedir, "data")

    journalist_1 = factory.User(id=1)
    journalist_2 = factory.User(id=2)
    session.add(journalist_1)
    session.add(journalist_2)

    source = factory.Source()
    session.add(source)
    session.commit()

    # Create a local file that will be updated to match the remote file object with the same uuid.
    local_file_to_update = factory.File(source_id=source.id, source=source)
    session.add(local_file_to_update)

    # Create a local file that will be deleted when there is no remote file object with the same
    # uuid.
    local_file_to_delete = factory.File(source_id=source.id, source=source)
    session.add(local_file_to_delete)
    session.commit()
    seen_record_to_delete = db.SeenFile(
        file_id=local_file_to_delete.id, journalist_id=journalist_1.id
    )
    session.add(seen_record_to_delete)
    session.commit()

    local_files = [local_file_to_update, local_file_to_delete]

    # Create a remote file that will be used to update one of the local replies.
    remote_file_to_update = factory.RemoteFile(
        uuid=local_file_to_update.uuid,
        source_uuid=source.uuid,
        seen_by=[journalist_1.uuid, journalist_2.uuid],
    )

    # Create a remote file that will be used to create a new local file.
    remote_file_to_create = factory.RemoteFile(
        source_uuid=source.uuid,
        source_url="/api/v1/sources/{}".format(source.uuid),
        file_counter=factory.FILE_COUNT + 1,
        filename="{}-doc.gz.gpg".format(factory.FILE_COUNT + 1),
        seen_by=[journalist_1.uuid, journalist_2.uuid],
    )

    # Create a remote file that was seen by a journalist without an account.
    remote_file_to_create_with_unknown_journalist = factory.RemoteFile(
        source_uuid=source.uuid,
        source_url="/api/v1/sources/{}".format(source.uuid),
        file_counter=factory.FILE_COUNT + 2,
        filename="{}-doc.gz.gpg".format(factory.FILE_COUNT + 2),
        seen_by=["unknown-journalist-uuid"],
    )

    remote_files = [
        remote_file_to_update,
        remote_file_to_create,
        remote_file_to_create_with_unknown_journalist,
    ]

    update_files(remote_files, local_files, session, data_dir)

    assert (
        session.query(db.SeenFile)
        .filter_by(file_id=local_file_to_update.id, journalist_id=journalist_1.id)
        .count()
        == 1
    )
    assert (
        session.query(db.SeenFile)
        .filter_by(file_id=local_file_to_update.id, journalist_id=journalist_2.id)
        .count()
        == 1
    )

    new_file = session.query(db.File).filter_by(uuid=remote_file_to_create.uuid).one()
    assert (
        session.query(db.SeenFile)
        .filter_by(file_id=new_file.id, journalist_id=journalist_1.id)
        .count()
        == 1
    )
    assert (
        session.query(db.SeenFile)
        .filter_by(file_id=new_file.id, journalist_id=journalist_2.id)
        .count()
        == 1
    )
    assert session.query(db.File).filter_by(uuid=local_file_to_delete.uuid).count() == 0
    assert session.query(db.SeenFile).filter_by(file_id=local_file_to_delete.id).count() == 0

    new_file_seen_by_unknown_journalist = (
        session.query(db.File)
        .filter_by(uuid=remote_file_to_create_with_unknown_journalist.uuid)
        .one()
    )
    assert (
        session.query(db.SeenFile).filter_by(file_id=new_file_seen_by_unknown_journalist.id).count()
        == 0
    )


def test_update_files_marks_read_files_as_seen_without_seen_records(homedir, mocker, session):
    """
    Check that the file submission without a seen record still returns true for "seen" if is_read is
    set.
    """
    data_dir = os.path.join(homedir, "data")

    source = factory.Source()
    session.add(source)
    session.commit()

    # Create a local file that will be updated to match the remote file object with the same uuid.
    local_file_to_update = factory.File(source_id=source.id, source=source)
    session.add(local_file_to_update)
    session.commit()
    local_files = [local_file_to_update]

    # Create a remote file that will be used to update one of the local files.
    remote_file_to_update = factory.RemoteFile(
        uuid=local_file_to_update.uuid, source_uuid=source.uuid, is_read=1
    )

    # Create a remote file that will be used to create a new local file.
    remote_file_to_create = factory.RemoteFile(
        source_uuid=source.uuid,
        source_url="/api/v1/sources/{}".format(source.uuid),
        file_counter=factory.FILE_COUNT + 1,
        filename="{}-doc.gz.gpg".format(factory.FILE_COUNT + 1),
        is_read=1,
    )

    remote_files = [
        remote_file_to_update,
        remote_file_to_create,
    ]

    update_files(remote_files, local_files, session, data_dir)

    new_local_file = session.query(db.File).filter_by(uuid=remote_file_to_create.uuid).one()

    assert new_local_file.is_read
    assert new_local_file.seen

    updated_local_file = session.query(db.File).filter_by(uuid=remote_file_to_update.uuid).one()

    assert updated_local_file.is_read
    assert updated_local_file.seen


def test_update_messages(homedir, mocker):
    """
    Check that:

    * Existing messages are updated in the local database.
    * New messages have an entry in the local database.
    * Local messages not returned by the remote server are deleted from the local database.
    """
    data_dir = os.path.join(homedir, "data")
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
    local_filename = "originalsubmissionname.txt"
    local_message_update.filename = local_filename
    local_message_update.is_downloaded = True
    local_message_update.is_decrypted = False
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
    mock_session.query().filter_by().first.return_value = local_source
    mock_focu = mocker.MagicMock(return_value=local_user)
    mocker.patch("securedrop_client.storage.create_or_update_user", mock_focu)
    mock_delete_submission_files = mocker.patch(
        "securedrop_client.storage.delete_single_submission_or_reply_on_disk"
    )

    update_messages(remote_messages, local_messages, mock_session, data_dir)

    # Check the expected local message object has been updated with values
    # from the API.
    assert local_message_update.filename == local_filename
    assert local_message_update.size == remote_message_update.size

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
    mock_delete_submission_files.assert_called_once_with(local_message_delete, data_dir)
    # Session is committed to database.
    assert mock_session.commit.call_count == 1


def test_update_messages_marks_read_messages_as_seen_without_seen_records(homedir, mocker, session):
    """
    Check that the file submission without a seen record still returns true for "seen" if is_read is
    set.
    """
    data_dir = os.path.join(homedir, "data")

    source = factory.Source()
    session.add(source)
    session.commit()

    # Create a local message that will be updated to match the remote file object with the same uuid
    local_message_to_update = factory.Message(source_id=source.id, source=source)
    session.add(local_message_to_update)
    session.commit()
    local_messages = [local_message_to_update]

    # Create a remote file that will be used to update one of the local files.
    remote_message_to_update = factory.RemoteMessage(
        uuid=local_message_to_update.uuid, source_uuid=source.uuid, is_read=1
    )

    # Create a remote file that will be used to create a new local file.
    remote_message_to_create = factory.RemoteMessage(
        source_uuid=source.uuid,
        source_url="/api/v1/sources/{}".format(source.uuid),
        file_counter=factory.FILE_COUNT + 1,
        filename="{}-msg.gpg".format(factory.FILE_COUNT + 1),
        is_read=1,
    )

    remote_messages = [
        remote_message_to_update,
        remote_message_to_create,
    ]

    update_messages(remote_messages, local_messages, session, data_dir)

    new_local_message = (
        session.query(db.Message).filter_by(uuid=remote_message_to_create.uuid).one()
    )

    assert new_local_message.is_read
    assert new_local_message.seen

    updated_local_message = (
        session.query(db.Message).filter_by(uuid=remote_message_to_update.uuid).one()
    )

    assert updated_local_message.is_read
    assert updated_local_message.seen


def test_update_messages_adds_seen_record(homedir, mocker, session):
    """
    Check that:

    * A seen record is created for each journalist in the seen_by field for an existing message.
    * A seen record is created for each journalist in the seen_by field for a new message.
    * Seen records for a deleted message are also deleted.
    * No seen record is created for a journalist without an account.
    """
    data_dir = os.path.join(homedir, "data")

    journalist_1 = factory.User(id=1)
    journalist_2 = factory.User(id=2)
    session.add(journalist_1)
    session.add(journalist_2)

    source = factory.Source()
    session.add(source)
    session.commit()

    # Create a local message that will be updated to match the remote message object with the same
    # uuid.
    local_message_to_update = factory.Message(source_id=source.id, source=source)
    session.add(local_message_to_update)

    # Create a local message that will be deleted when there is no remote message object with the
    # same uuid.
    local_message_to_delete = factory.Message(source_id=source.id, source=source)
    session.add(local_message_to_delete)
    session.commit()
    seen_record_to_delete = db.SeenMessage(
        message_id=local_message_to_delete.id, journalist_id=journalist_1.id
    )
    session.add(seen_record_to_delete)
    session.commit()

    local_messages = [local_message_to_update, local_message_to_delete]

    # Create a remote message that will be used to update one of the local replies.
    remote_message_to_update = factory.RemoteMessage(
        uuid=local_message_to_update.uuid,
        source_uuid=source.uuid,
        seen_by=[journalist_1.uuid, journalist_2.uuid],
    )

    # Create a remote message that will be used to create a new local message.
    remote_message_to_create = factory.RemoteMessage(
        source_uuid=source.uuid,
        source_url="/api/v1/sources/{}".format(source.uuid),
        file_counter=factory.MESSAGE_COUNT + 1,
        filename="{}-msg.gpg".format(factory.MESSAGE_COUNT + 1),
        seen_by=[journalist_1.uuid, journalist_2.uuid],
    )

    # Create a remote message that was seen by a journalist without an account.
    remote_message_t0_create_with_unknown_journalist = factory.RemoteMessage(
        source_uuid=source.uuid,
        source_url="/api/v1/sources/{}".format(source.uuid),
        file_counter=factory.MESSAGE_COUNT + 2,
        filename="{}-msg.gpg".format(factory.MESSAGE_COUNT + 2),
        seen_by=["unknown-journalist-uuid"],
    )

    remote_messages = [
        remote_message_to_update,
        remote_message_to_create,
        remote_message_t0_create_with_unknown_journalist,
    ]

    update_messages(remote_messages, local_messages, session, data_dir)

    assert (
        session.query(db.SeenMessage)
        .filter_by(message_id=local_message_to_update.id, journalist_id=journalist_1.id)
        .count()
        == 1
    )
    assert (
        session.query(db.SeenMessage)
        .filter_by(message_id=local_message_to_update.id, journalist_id=journalist_2.id)
        .count()
        == 1
    )

    new_message = session.query(db.Message).filter_by(uuid=remote_message_to_create.uuid).one()
    assert (
        session.query(db.SeenMessage)
        .filter_by(message_id=new_message.id, journalist_id=journalist_1.id)
        .count()
        == 1
    )
    assert (
        session.query(db.SeenMessage)
        .filter_by(message_id=new_message.id, journalist_id=journalist_2.id)
        .count()
        == 1
    )
    assert session.query(db.Message).filter_by(uuid=local_message_to_delete.uuid).count() == 0
    assert (
        session.query(db.SeenMessage).filter_by(message_id=local_message_to_delete.id).count() == 0
    )

    new_message_seen_by_unknown_journalist = (
        session.query(db.Message)
        .filter_by(uuid=remote_message_t0_create_with_unknown_journalist.uuid)
        .one()
    )
    assert (
        session.query(db.SeenMessage)
        .filter_by(message_id=new_message_seen_by_unknown_journalist.id)
        .count()
        == 0
    )


def test_update_replies(homedir, mocker, session):
    """
    Check that:

    * Existing replies are updated in the local database.
    * New replies have an entry in the local database.
    * Local replies not returned by the remote server are deleted from the local database.
    * References to journalist's usernames are correctly handled.
    """
    data_dir = os.path.join(homedir, "data")

    journalist = factory.User(id=1)
    session.add(journalist)

    source = factory.Source()
    session.add(source)

    # Create a local reply that will be updated to match the remote reply object with the same uuid.
    local_reply_update = factory.Reply(
        source_id=source.id,
        source=source,
        journalist_id=journalist.id,
        filename="1-original-reply.gpg",
        size=2,
    )
    session.add(local_reply_update)

    # Create a local reply that will be deleted when there is no remote reply object with the same
    # uuid.
    local_reply_delete = factory.Reply(source_id=source.id, source=source)
    session.add(local_reply_delete)

    local_replies = [local_reply_update, local_reply_delete]

    # Create a remote reply that will be used to update one of the local replies.
    remote_reply_update = factory.RemoteReply(
        uuid=local_reply_update.uuid,
        journalist_uuid=journalist.uuid,
        journalist_first_name="new_name",
        journalist_last_name="new_name",
        source_url="/api/v1/sources/{}".format(source.uuid),
        file_counter=local_reply_update.file_counter,
        filename=local_reply_update.filename,
        seen_by=[],
    )

    # Create a remote reply that will be used to create a new local reply.
    remote_reply_create = factory.RemoteReply(
        journalist_uuid=journalist.uuid,
        source_url="/api/v1/sources/{}".format(source.uuid),
        file_counter=factory.REPLY_COUNT + 1,
        filename="{}-filename.gpg".format(factory.REPLY_COUNT + 1),
        journalist_first_name="",
        journalist_last_name="",
        seen_by=[],
    )

    remote_replies = [remote_reply_update, remote_reply_create]

    update_replies(remote_replies, local_replies, session, data_dir)

    # Check the expected local reply object has been updated with values
    # from the API.
    assert local_reply_update.journalist_id == journalist.id
    assert local_reply_update.size == remote_reply_update.size
    assert local_reply_update.filename == remote_reply_update.filename

    new_reply = session.query(db.Reply).filter_by(uuid=remote_reply_create.uuid).one()
    assert new_reply.source_id == source.id
    assert new_reply.journalist_id == journalist.id
    assert new_reply.size == remote_reply_create.size
    assert new_reply.filename == remote_reply_create.filename

    # Ensure the local reply that is not in the API results is deleted.
    assert session.query(db.Reply).filter_by(uuid=local_reply_delete.uuid).count() == 0


def test_update_replies_adds_seen_record(homedir, mocker, session):
    """
    Check that:

    * A seen record is created for each journalist in the seen_by field for an existing reply.
    * A seen record is created for each journalist in the seen_by field for a new reply.
    * Seen records for a deleted reply are also deleted.
    * No seen record is created for a journalist without an account.
    """
    data_dir = os.path.join(homedir, "data")

    journalist_1 = factory.User(id=1)
    journalist_2 = factory.User(id=2)
    session.add(journalist_1)
    session.add(journalist_2)

    source = factory.Source()
    session.add(source)

    # Create a local reply that will be updated to match the remote reply object with the same uuid.
    local_reply_to_update = factory.Reply(source_id=source.id, source=source)
    session.add(local_reply_to_update)

    # Create a local reply that will be deleted when there is no remote reply object with the same
    # uuid.
    local_reply_to_delete = factory.Reply(source_id=source.id, source=source)
    session.add(local_reply_to_delete)
    session.commit()
    seen_record_to_delete = db.SeenReply(
        reply_id=local_reply_to_delete.id, journalist_id=journalist_1.id
    )
    session.add(seen_record_to_delete)
    session.commit()

    local_replies = [local_reply_to_update, local_reply_to_delete]

    # Create a remote reply that will be used to update one of the local replies.
    remote_reply_update = factory.RemoteReply(
        uuid=local_reply_to_update.uuid,
        journalist_uuid=journalist_1.uuid,
        seen_by=[journalist_1.uuid, journalist_2.uuid],
    )

    # Create a remote reply that will be used to create a new local reply.
    remote_reply_create = factory.RemoteReply(
        journalist_uuid=journalist_1.uuid,
        source_url="/api/v1/sources/{}".format(source.uuid),
        file_counter=factory.REPLY_COUNT + 1,
        filename="{}-reply.gpg".format(factory.REPLY_COUNT + 1),
        seen_by=[journalist_1.uuid, journalist_2.uuid],
    )

    # Create a remote reply that was seen by a journalist without an account.
    remote_reply_to_create_with_unknown_journalist = factory.RemoteReply(
        journalist_uuid=journalist_1.uuid,
        source_url="/api/v1/sources/{}".format(source.uuid),
        file_counter=factory.REPLY_COUNT + 2,
        filename="{}-reply.gpg".format(factory.REPLY_COUNT + 2),
        seen_by=["unknown-journalist-uuid"],
    )

    remote_replies = [
        remote_reply_update,
        remote_reply_create,
        remote_reply_to_create_with_unknown_journalist,
    ]

    update_replies(remote_replies, local_replies, session, data_dir)

    assert (
        session.query(db.SeenReply)
        .filter_by(reply_id=local_reply_to_update.id, journalist_id=journalist_1.id)
        .count()
        == 1
    )
    assert (
        session.query(db.SeenReply)
        .filter_by(reply_id=local_reply_to_update.id, journalist_id=journalist_2.id)
        .count()
        == 1
    )

    new_reply = session.query(db.Reply).filter_by(uuid=remote_reply_create.uuid).one()
    assert (
        session.query(db.SeenReply)
        .filter_by(reply_id=new_reply.id, journalist_id=journalist_1.id)
        .count()
        == 1
    )
    assert (
        session.query(db.SeenReply)
        .filter_by(reply_id=new_reply.id, journalist_id=journalist_2.id)
        .count()
        == 1
    )
    assert session.query(db.Reply).filter_by(uuid=local_reply_to_delete.uuid).count() == 0
    assert session.query(db.SeenReply).filter_by(reply_id=local_reply_to_delete.id).count() == 0

    new_reply_seen_by_unknown_journalist = (
        session.query(db.Reply)
        .filter_by(uuid=remote_reply_to_create_with_unknown_journalist.uuid)
        .one()
    )
    assert (
        session.query(db.SeenReply)
        .filter_by(reply_id=new_reply_seen_by_unknown_journalist.id)
        .count()
        == 0
    )


def test_update_replies_cleanup_drafts(homedir, mocker, session):
    """
    Check that draft replies are deleted if they correspond to a reply fetched from
    the server.
    """
    data_dir = os.path.join(homedir, "data")
    # Source object related to the submissions.
    source = factory.Source()
    user = factory.User()
    session.add(source)
    session.add(user)
    session.commit()

    # One reply will exist on the server.
    remote_reply_create = make_remote_reply(source.uuid, "hehe")
    remote_replies = [remote_reply_create]

    # One draft reply will exist in the local database corresponding to the server reply.
    draft_reply = db.DraftReply(
        uuid=remote_reply_create.uuid,
        source=source,
        journalist=user,
        file_counter=3,
        timestamp=datetime.datetime(2000, 6, 6, 6, 0),
    )
    session.add(draft_reply)
    # Another draft reply will exist that should be moved to _after_ the new reply
    # once we confirm the previous reply. This ensures consistent ordering of interleaved
    # drafts (pending and failed) with replies, messages, and files from the user's perspective.
    draft_reply_new = db.DraftReply(
        uuid="foo",
        source=source,
        journalist=user,
        file_counter=3,
        timestamp=datetime.datetime(2001, 6, 6, 6, 0),
    )
    session.add(draft_reply_new)
    session.commit()

    # We have no replies locally stored.
    local_replies = []

    update_replies(remote_replies, local_replies, session, data_dir)

    # Check the expected local source object has been created.
    new_local_replies = session.query(db.Reply).all()
    assert len(new_local_replies) == 1

    # Check that the only draft is the one sent with uuid 'foo' and its file_counter now
    # matches the file_counter of the updated reply. This ensures consistent ordering.
    new_draft_replies = session.query(db.DraftReply).all()
    assert len(new_draft_replies) == 1
    assert new_draft_replies[0].file_counter == new_local_replies[0].file_counter
    assert new_draft_replies[0].uuid == draft_reply_new.uuid


def test_update_replies_missing_source(homedir, mocker, session):
    """
    Verify that a reply to an invalid source is handled.
    """
    data_dir = os.path.join(homedir, "data")

    journalist = factory.User(id=1)
    session.add(journalist)

    source = factory.Source()
    session.add(source)

    # Some remote reply objects from the API, one of which will exist in the
    # local database, the other will NOT exist in the local database
    # (this will be added to the database)
    remote_reply = make_remote_reply("nonexistent-source", journalist.uuid)
    remote_replies = [remote_reply]
    local_replies = []

    error_logger = mocker.patch("securedrop_client.storage.logger.error")

    update_replies(remote_replies, local_replies, session, data_dir)

    error_logger.assert_called_once_with(f"No source found for reply {remote_reply.uuid}")


def test_User_deleted(mocker, session):
    """
    Test deleted User..
    """
    user = create_or_update_user("deleted", "mock", "mock", "mock", session)
    assert not user.initials
    assert not user.fullname
    assert user.deleted


def test_create_or_update_user_existing_uuid(mocker):
    """
    Return an existing user object with the referenced uuid.
    """
    mock_session = mocker.MagicMock()
    mock_user = mocker.MagicMock()
    mock_user.username = "foobar"
    mock_user.firstname = "foobar"
    mock_user.lastname = "foobar"
    mock_session.query().filter_by().one_or_none.return_value = mock_user
    assert create_or_update_user("uuid", "username", "fn", "ln", mock_session) == mock_user


def test_create_or_update_user_update_username(mocker, session):
    """
    Return an existing user object with the updated username.
    """
    user = factory.User(uuid="mock_uuid", username="mock_old_username")
    session.add(user)

    actual_user = create_or_update_user("mock_uuid", "mock_username", "fn", "ln", session)

    assert actual_user == user
    assert actual_user.username == "mock_username"
    assert actual_user.firstname == "fn"
    assert actual_user.lastname == "ln"


def test_create_or_update_user_new(mocker):
    """
    Create and return a user object for an unknown username.
    """
    mock_session = mocker.MagicMock()
    mock_session.query().filter_by().one_or_none.return_value = None
    new_user = create_or_update_user("uuid", "unknown", "unknown", "unknown", mock_session)
    assert new_user.username == "unknown"
    mock_session.add.assert_called_once_with(new_user)
    mock_session.commit.assert_called_once_with()


def test_create_or_update_user(mocker, session):
    """
    Return an existing user object with the updated username, firstname, and lastname.
    """
    user = factory.User(
        uuid="mock_uuid",
        username="mock_old_username",  # username is needed for create_or_update_user
        firstname="mock_old_firstname",
        lastname="mock_old_lastname",
    )
    session.add(user)

    updated_user = create_or_update_user(
        uuid="mock_uuid",
        username="mock_username",
        firstname="mock_firstname",
        lastname="mock_lastname",
        session=session,
    )

    assert updated_user.username == "mock_username"
    assert updated_user.firstname == "mock_firstname"
    assert updated_user.lastname == "mock_lastname"


def test_find_new_messages(mocker, session):
    source = factory.Source()
    message_not_downloaded = factory.Message(
        source=source, is_downloaded=False, is_decrypted=None, content=None
    )
    message_decrypt_not_attempted = factory.Message(
        source=source, is_downloaded=True, is_decrypted=None, content=None
    )
    message_decrypt_failed = factory.Message(
        source=source, is_downloaded=True, is_decrypted=False, content=None
    )
    message_decrypt_success = factory.Message(
        source=source, is_downloaded=True, is_decrypted=True, content="teehee"
    )
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


def test_update_missing_files(mocker, homedir):
    session = mocker.MagicMock()
    file = mocker.MagicMock()
    file.is_downloaded = True
    files = [file]
    session.query().filter_by().all.return_value = files
    data_dir = os.path.join(homedir, "data")
    mocker.patch("os.path.splitext", return_value=("mock_filename", "dummy"))
    mocker.patch("os.path.exists", return_value=False)
    mark_as_not_downloaded_fn = mocker.patch("securedrop_client.storage.mark_as_not_downloaded")

    update_missing_files(data_dir, session)

    mark_as_not_downloaded_fn.assert_called_once_with(file.uuid, session)


def test_find_new_files(mocker, session):
    mock_session = mocker.MagicMock()
    mock_submission = mocker.MagicMock()
    mock_submission.is_downloaded = False
    mock_submissions = [mock_submission]
    mock_session.query().join().filter_by().order_by().all.return_value = mock_submissions
    submissions = find_new_files(mock_session)
    assert submissions[0].is_downloaded is False


def test_find_new_replies(mocker, session):
    source = factory.Source()
    reply_not_downloaded = factory.Reply(
        source=source, is_downloaded=False, is_decrypted=None, content=None
    )
    reply_decrypt_not_attempted = factory.Reply(
        source=source, is_downloaded=True, is_decrypted=None, content=None
    )
    reply_decrypt_failed = factory.Reply(
        source=source, is_downloaded=True, is_decrypted=False, content=None
    )
    reply_decrypt_success = factory.Reply(
        source=source, is_downloaded=True, is_decrypted=True, content="teehee"
    )
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


def test_set_file_decryption_status_with_content_null_to_false(mocker, session):
    file = factory.File(source=factory.Source(), is_decrypted=None)
    session.add(file)
    session.commit()

    mark_as_decrypted(type(file), file.uuid, session, False)

    assert file.is_decrypted is False


def test_set_file_decryption_status_with_content_false_to_true(mocker, session):
    file = factory.File(source=factory.Source(), is_downloaded=True, is_decrypted=False)
    session.add(file)
    session.commit()

    mark_as_decrypted(type(file), file.uuid, session)

    assert file.is_decrypted is True


def test_set_message_decryption_status_with_content_with_content(session, source):
    """
    It should be possible to set the decryption status of an object in the database to `True`.
    Additionally, if `content` is passed in, the `content` column of the DB should take that
    value. This is to ensure that we have a way to decrypt something without violating the
    condition: if is_decrypted then content is not none.
    """
    message = factory.Message(
        source=source["source"], is_downloaded=True, is_decrypted=None, content=None
    )
    session.add(message)
    session.commit()

    set_message_or_reply_content(type(message), message.uuid, "mock_content", session)
    mark_as_decrypted(type(message), message.uuid, session)

    # requery to ensure new object
    message = session.query(db.Message).get(message.id)
    assert message.is_decrypted is True
    assert message.content == "mock_content"


def test_mark_file_as_not_downloaded(mocker):
    session = mocker.MagicMock()
    file = factory.File(source=factory.Source(), is_downloaded=True, is_decrypted=True)
    session.query().filter_by().one.return_value = file
    mark_as_not_downloaded("mock_uuid", session)
    assert file.is_downloaded is False
    assert file.is_decrypted is None
    session.add.assert_called_once_with(file)
    session.commit.assert_called_once_with()


def test_mark_file_as_downloaded(mocker):
    session = mocker.MagicMock()
    file = factory.File(source=factory.Source(), is_downloaded=False)
    session.query().filter_by().one.return_value = file
    mark_as_downloaded(type(file), "mock_uuid", session)
    assert file.is_downloaded is True
    session.add.assert_called_once_with(file)
    session.commit.assert_called_once_with()


def test_mark_message_as_downloaded(mocker):
    session = mocker.MagicMock()
    message = factory.Message(source=factory.Source(), is_downloaded=False)
    session.query().filter_by().one.return_value = message
    mark_as_downloaded(type(message), "mock_uuid", session)
    assert message.is_downloaded is True
    session.add.assert_called_once_with(message)
    session.commit.assert_called_once_with()


def test_mark_reply_as_downloaded(mocker):
    session = mocker.MagicMock()
    reply = factory.Reply(source=factory.Source(), is_downloaded=False)
    session.query().filter_by().one.return_value = reply
    mark_as_downloaded(type(reply), "mock_uuid", session)
    assert reply.is_downloaded is True
    session.add.assert_called_once_with(reply)
    session.commit.assert_called_once_with()


def test_delete_single_submission_or_reply_race_guard(homedir, mocker):
    """
    This test checks that if there is a file is deleted
    locally through another method, that an unhandled exception
    will not occur in delete_single_submission_or_reply_on_disk
    """

    test_obj = mocker.MagicMock()
    test_obj.filename = "1-dissolved-steak-msg.gpg"
    add_test_file_to_temp_dir(homedir, test_obj.filename)

    mock_remove = mocker.patch("os.remove", side_effect=FileNotFoundError)
    delete_single_submission_or_reply_on_disk(test_obj, homedir)

    mock_remove.call_count == 1


def test_delete_single_submission_or_reply_single_file(homedir, mocker):
    """
    This test checks that calling the delete_single_submission_or_reply
    method deletes the file as well as the folder it's inside.
    """

    source = factory.Source(journalist_designation="dissolved-steak")
    file_server_filename = "1-dissolved-steak-msg.gpg"
    test_obj = db.File(
        source=source,
        uuid="test",
        size=123,
        filename=file_server_filename,
        download_url="http://test/test",
    )
    source_directory = os.path.dirname(test_obj.location(homedir))
    add_test_file_to_temp_dir(source_directory, file_server_filename)

    delete_single_submission_or_reply_on_disk(test_obj, homedir)

    # Ensure both file and its containing folder are gone.
    with pytest.raises(FileNotFoundError):
        open(os.path.join(source_directory, file_server_filename), "r")

    with pytest.raises(FileNotFoundError):
        open(source_directory, "r")


def test_delete_single_submission_or_reply_single_file_no_folder(homedir, mocker):
    """
    This test checks that calling the delete_single_submission_or_reply
    method deletes the file even if its not in a per-document folder.
    """

    source = factory.Source(journalist_designation="dissolved-steak")
    file_server_filename = "1-dissolved-steak-msg.gpg"
    test_obj = db.File(
        source=source,
        uuid="test",
        size=123,
        filename=file_server_filename,
        download_url="http://test/test",
    )
    original_location = test_obj.location
    test_obj.location = mocker.MagicMock(
        side_effect=[os.path.join(homedir, file_server_filename), original_location(homedir)]
    )
    add_test_file_to_temp_dir(homedir, file_server_filename)

    delete_single_submission_or_reply_on_disk(test_obj, homedir)

    with pytest.raises(FileNotFoundError):
        open(os.path.join(homedir, file_server_filename), "r")


def test_source_exists_true(homedir, mocker):
    """
    Check that method returns True if a source is return from the query.
    """
    session = mocker.MagicMock()
    source = factory.RemoteSource()
    source.uuid = "test-source-uuid"
    session.query().filter_by().one.return_value = source
    assert source_exists(session, "test-source-uuid")


def test_source_exists_false(homedir, mocker):
    """
    Check that method returns False if NoResultFound is thrown when we try to query the source.
    """
    session = mocker.MagicMock()
    source = mocker.MagicMock()
    source.uuid = "test-source-uuid"
    session.query().filter_by().one.side_effect = NoResultFound()

    assert not source_exists(session, "test-source-uuid")


def test_get_file(mocker, session):
    source = factory.Source()
    file = factory.File(source=source)
    session.add(source)
    session.add(file)

    result = get_file(session, file.uuid)

    assert result == file


def test_get_message(mocker, session):
    source = factory.Source()
    message = factory.Message(source=source)
    session.add(source)
    session.add(message)

    result = get_message(session, message.uuid)

    assert result == message


def test_get_reply(mocker, session):
    source = factory.Source()
    reply = factory.Reply(source=source)
    session.add(source)
    session.add(reply)

    result = get_reply(session, reply.uuid)

    assert result == reply


def test_pending_replies_are_marked_as_failed_on_logout_login(mocker, session, reply_status_codes):
    source = factory.Source()
    pending_status = (
        session.query(db.ReplySendStatus)
        .filter_by(name=db.ReplySendStatusCodes.PENDING.value)
        .one()
    )
    failed_status = (
        session.query(db.ReplySendStatus).filter_by(name=db.ReplySendStatusCodes.FAILED.value).one()
    )
    pending_draft_reply = factory.DraftReply(source=source, send_status=pending_status)
    session.add(source)
    session.add(pending_draft_reply)

    mark_all_pending_drafts_as_failed(session)

    for draft in session.query(db.DraftReply).all():
        assert draft.send_status == failed_status


def test_update_file_size(homedir, session):
    source = factory.Source()
    f = factory.File(source=source)
    session.add(f)
    session.commit()

    real_size = 2112
    data_dir = os.path.join(homedir, "data")
    file_location = f.location(data_dir)

    os.makedirs(os.path.dirname(file_location), mode=0o700, exist_ok=True)
    with open(file_location, mode="w") as f1:
        f1.write("x" * real_size)
    update_file_size(f.uuid, data_dir, session)

    assert f.size == real_size


def test_update_draft_replies_commit(mocker, session):
    """
    Tests the commit argument of storage.update_draft_replies.
    """
    session.commit = mocker.MagicMock()

    update_draft_replies(session, "notreal", datetime.datetime.now(), 1, 2, commit=False)
    assert session.commit.call_count == 0

    update_draft_replies(session, "notreal", datetime.datetime.now(), 1, 2)
    assert session.commit.call_count == 1
