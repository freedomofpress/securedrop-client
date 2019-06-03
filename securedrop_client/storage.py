"""
Functions needed to synchronise data with the SecureDrop server (via the
securedrop_sdk). Each function requires but two arguments: an authenticated
instance of the securedrop_sdk API class, and a SQLAlchemy session to the local
database.

Copyright (C) 2018  The Freedom of the Press Foundation.

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published
by the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
"""
import logging
import glob
import os
from dateutil.parser import parse
from typing import List, Tuple, Type, Union

from sqlalchemy import or_
from securedrop_client.db import session_scope, Source, Message, File, Reply, User
from sdclientapi import API
from sdclientapi import Source as SDKSource
from sdclientapi import Submission as SDKSubmission
from sdclientapi import Reply as SDKReply

logger = logging.getLogger(__name__)


def get_local_sources() -> List[Source]:
    """
    Return all source objects from the local database.
    """
    with session_scope() as session:
        sources = session.query(Source).all()
        session.close()
        return sources


def add_reply(reply_uuid, source_uuid, journalist_uuid, filename):
    """
    Add a reply to the database.
    """
    with session_scope() as session:
        source = session.query(Source).filter_by(uuid=source_uuid).one_or_none()
        reply = Reply(
            uuid=reply_uuid,
            source_id=source.id,
            journalist_id=journalist_uuid,
            filename=filename)
        session.add(reply)


def get_remote_data(api: API) -> Tuple[List[SDKSource], List[SDKSubmission], List[SDKReply]]:
    """
    Given an authenticated connection to the SecureDrop API, get sources,
    submissions and replies from the remote server and return a tuple
    containing lists of objects representing this data:

    (remote_sources, remote_submissions, remote_replies)
    """
    remote_submissions = []  # type: List[SDKSubmission]
    try:
        remote_sources = api.get_sources()
        for source in remote_sources:
            remote_submissions.extend(api.get_submissions(source))
        remote_replies = api.get_all_replies()
    except Exception as ex:
        # Log any errors but allow the caller to handle the exception.
        logger.error(ex)
        raise(ex)

    logger.info('Fetched {} remote sources.'.format(len(remote_sources)))
    logger.info('Fetched {} remote submissions.'.format(
        len(remote_submissions)))
    logger.info('Fetched {} remote replies.'.format(len(remote_replies)))

    return (remote_sources, remote_submissions, remote_replies)


def update_local_storage(remote_sources: List[SDKSource],
                         remote_submissions: List[SDKSubmission],
                         remote_replies: List[SDKReply], data_dir: str) -> None:
    """
    Given a database session and collections of remote sources, submissions and
    replies from the SecureDrop API, ensures the local database is updated
    with this data.
    """
    remote_messages = [x for x in remote_submissions if x.filename.endswith('msg.gpg')]
    remote_files = [x for x in remote_submissions if not x.filename.endswith('msg.gpg')]

    update_sources(remote_sources, data_dir)
    update_files(remote_files, data_dir)
    update_messages(remote_messages, data_dir)
    update_replies(remote_replies, data_dir)


def update_sources(remote_sources: List[SDKSource], data_dir: str) -> None:
    """
    Given collections of remote sources, the current local sources and a
    session to the local database, ensure the state of the local database
    matches that of the remote sources:

    * Existing items are updated in the local database.
    * New items are created in the local database.
    * Local items not returned in the remote sources are deleted from the
      local database.
    """
    with session_scope() as session:
        local_sources = session.query(Source).all()
        local_uuids = {source.uuid for source in local_sources}
        for source in remote_sources:
            if source.uuid in local_uuids:
                # Update an existing record.
                local_source = [s for s in local_sources if s.uuid == source.uuid][0]
                local_source.journalist_designation = source.journalist_designation
                local_source.is_flagged = source.is_flagged
                local_source.public_key = source.key['public']
                local_source.interaction_count = source.interaction_count
                local_source.document_count = source.number_of_documents
                local_source.is_starred = source.is_starred
                local_source.last_updated = parse(source.last_updated)

                # Removing the UUID from local_uuids ensures this record won't be
                # deleted at the end of this function.
                local_uuids.remove(source.uuid)
                logger.debug('Updated source {}'.format(source.uuid))
            else:
                # A new source to be added to the database.
                ns = Source(uuid=source.uuid,
                            journalist_designation=source.journalist_designation,
                            is_flagged=source.is_flagged,
                            public_key=source.key['public'],
                            interaction_count=source.interaction_count,
                            is_starred=source.is_starred,
                            last_updated=parse(source.last_updated),
                            document_count=source.number_of_documents)
                session.add(ns)
                logger.debug('Added new source {}'.format(source.uuid))

        # The uuids remaining in local_uuids do not exist on the remote server, so
        # delete the related records.
        for deleted_source in [s for s in local_sources if s.uuid in local_uuids]:
            for document in deleted_source.collection:
                delete_single_submission_or_reply_on_disk(document, data_dir)

            session.delete(deleted_source)
            logger.debug('Deleted source {}'.format(deleted_source.uuid))


def update_files(remote_submissions: List[SDKSubmission], data_dir: str) -> None:
    __update_submissions(File, remote_submissions, data_dir)


def update_messages(remote_submissions: List[SDKSubmission], data_dir: str) -> None:
    __update_submissions(Message, remote_submissions, data_dir)


def __update_submissions(model: Union[Type[File], Type[Message]],
                         remote_submissions: List[SDKSubmission],
                         data_dir: str) -> None:
    """
    The logic for updating files and messages is effectively the same, so this function is somewhat
    overloaded to allow us to do both in a DRY way.

    * Existing submissions are updated in the local database.
    * New submissions have an entry created in the local database.
    * Local submissions not returned in the remote submissions are deleted
      from the local database.
    """
    with session_scope() as session:
        local_submissions = session.query(model).all()
        local_uuids = {submission.uuid for submission in local_submissions}
        for submission in remote_submissions:
            if submission.uuid in local_uuids:
                local_submission = [s for s in local_submissions
                                    if s.uuid == submission.uuid][0]

                # Update files on disk to match new filename.
                if (local_submission.filename != submission.filename):
                    rename_file(data_dir, local_submission.filename,
                                submission.filename)

                # Update an existing record.
                local_submission.filename = submission.filename
                local_submission.size = submission.size
                local_submission.is_read = submission.is_read
                local_submission.download_url = submission.download_url

                # Removing the UUID from local_uuids ensures this record won't be
                # deleted at the end of this function.
                local_uuids.remove(submission.uuid)
                logger.debug('Updated submission {}'.format(submission.uuid))
            else:
                # A new submission to be added to the database.
                _, source_uuid = submission.source_url.rsplit('/', 1)

                source = session.query(Source).filter_by(uuid=source_uuid)[0]
                ns = model(source_id=source.id, uuid=submission.uuid, size=submission.size,
                           filename=submission.filename, download_url=submission.download_url)
                session.add(ns)
                logger.debug('Added new submission {}'.format(submission.uuid))

        # The uuids remaining in local_uuids do not exist on the remote server, so
        # delete the related records.
        for deleted_submission in [s for s in local_submissions
                                   if s.uuid in local_uuids]:
            delete_single_submission_or_reply_on_disk(deleted_submission, data_dir)
            session.delete(deleted_submission)
            logger.debug('Deleted submission {}'.format(deleted_submission.uuid))


def update_replies(remote_replies: List[SDKReply], data_dir: str) -> None:
    """
    * Existing replies are updated in the local database.
    * New replies have an entry created in the local database.
    * Local replies not returned in the remote replies are deleted from the
      local database.

    If a reply references a new journalist username, add them to the database
    as a new user.
    """
    with session_scope() as session:
        local_replies = session.query(Reply).all()
        local_uuids = {reply.uuid for reply in local_replies}
        for reply in remote_replies:
            if reply.uuid in local_uuids:
                local_reply = [r for r in local_replies if r.uuid == reply.uuid][0]
                # Update files on disk to match new filename.
                if (local_reply.filename != reply.filename):
                    rename_file(data_dir, local_reply.filename, reply.filename)
                # Update an existing record.
                jid = get_journalist_id(reply.journalist_uuid, reply.journalist_username)
                local_reply.journalist_id = jid
                local_reply.filename = reply.filename
                local_reply.size = reply.size

                local_uuids.remove(reply.uuid)
                logger.debug('Updated reply {}'.format(reply.uuid))
            else:
                # A new reply to be added to the database.
                source_uuid = reply.source_uuid
                source = session.query(Source).filter_by(uuid=source_uuid)[0]
                jid = get_journalist_id(reply.journalist_uuid, reply.journalist_username)
                nr = Reply(uuid=reply.uuid,
                           journalist_id=jid,
                           source_id=source.id,
                           filename=reply.filename,
                           size=reply.size)
                session.add(nr)
                logger.debug('Added new reply {}'.format(reply.uuid))

        # The uuids remaining in local_uuids do not exist on the remote server, so
        # delete the related records.
        for deleted_reply in [r for r in local_replies if r.uuid in local_uuids]:
            delete_single_submission_or_reply_on_disk(deleted_reply, data_dir)
            session.delete(deleted_reply)
            logger.debug('Deleted reply {}'.format(deleted_reply.uuid))


def get_journalist_id(uuid: str, username: str) -> str:
    """
    Returns a user object representing the referenced journalist UUID.
    If the user does not already exist in the data, a new instance is created.
    If the user exists but the username has changed, the username is updated.
    """
    with session_scope() as session:
        user = session.query(User).filter_by(uuid=uuid).one_or_none()
        if user and user.username == username:
            # User exists in the local database and the username is unchanged.
            user_id = user.id
        elif user and user.username != username:
            # User exists in the local database but the username is changed.
            user.username = username
            session.add(user)
            user_id = user.id
        else:
            # User does not exist in the local database.
            new_user = User(username=username)
            new_user.uuid = uuid
            session.add(new_user)
            user_id = new_user.id
        session.close()
        return user_id


def find_new_messages() -> List[Message]:
    """
    Find messages to process. Those messages are those where one of the following
    conditions is true:

    * The message has not yet been downloaded.
    * The message has not yet had decryption attempted.
    * Decryption previously failed on a message.
    """
    with session_scope() as session:
        messages = session.query(Message).filter(
            or_(Message.is_downloaded == False,
                Message.is_decrypted == False,
                Message.is_decrypted == None)).all()  # noqa: E711
        session.close()
        return messages


def find_new_files() -> List[File]:
    with session_scope() as session:
        files = session.query(File).filter_by(is_downloaded=False).all()
        session.close()
        return files

def find_new_replies() -> List[Reply]:
    """
    Find replies to process. Those replies are those where one of the following
    conditions is true:

    * The reply has not yet been downloaded.
    * The reply has not yet had decryption attempted.
    * Decryption previously failed on a reply.
    """
    with session_scope() as session:
        replies = session.query(Reply).filter(
            or_(Reply.is_downloaded == False,
                Reply.is_decrypted == False,
                Reply.is_decrypted == None)).all()  # noqa: E711
        return replies


def mark_file_as_downloaded(uuid: str) -> None:
    """
    Mark file as downloaded in the database.
    """
    with session_scope() as session:
        file_db_object = session.query(File).filter_by(uuid=uuid).one()
        file_db_object.is_downloaded = True
        session.add(file_db_object)


def mark_message_as_downloaded(uuid: str) -> None:
    """
    Mark message as downloaded in the database.
    """
    with session_scope() as session:
        message_db_object = session.query(Message).filter_by(uuid=uuid).one()
        message_db_object.is_downloaded = True
        session.add(message_db_object)


def set_object_decryption_status_with_content(obj: Union[File, Message, Reply],
                                              is_successful: bool,
                                              content: str = None) -> None:
    """Mark object as decrypted or not in the database."""
    with session_scope() as session:
        model = type(obj)
        db_object = session.query(model).filter_by(uuid=obj.uuid).one_or_none()
        db_object.is_decrypted = is_successful
        if content is not None:
            db_object.content = content
        session.add(db_object)


def mark_reply_as_downloaded(uuid: str) -> None:
    """
    Mark reply as downloaded in the database.
    """
    with session_scope() as session:
        reply_db_object = session.query(Reply).filter_by(uuid=uuid).one()
        reply_db_object.is_downloaded = True
        session.add(reply_db_object)


def delete_single_submission_or_reply_on_disk(obj_db: Union[File, Message, Reply],
                                              data_dir: str) -> None:
    """
    Delete on disk a single submission or reply.
    """
    filename_without_extensions = obj_db.filename.split('.')[0]
    files_to_delete = os.path.join(
        data_dir,
        '{}*'.format(filename_without_extensions))
    logging.info('Deleting all {} files'.format(filename_without_extensions))

    try:
        for file_to_delete in glob.glob(files_to_delete):
            os.remove(file_to_delete)
    except FileNotFoundError:
        logging.info(
            'File {} already deleted, skipping'.format(file_to_delete))


def rename_file(data_dir: str, filename: str, new_filename: str) -> None:
    filename, _ = os.path.splitext(filename)
    new_filename, _ = os.path.splitext(new_filename)
    try:
        os.rename(os.path.join(data_dir, filename),
                  os.path.join(data_dir, new_filename))
    except OSError as e:
        logger.debug('File could not be renamed: {}'.format(e))
