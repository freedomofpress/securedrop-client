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
import os
import shutil
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Tuple, Type, Union

from dateutil.parser import parse
from sdclientapi import API
from sdclientapi import Reply as SDKReply
from sdclientapi import Source as SDKSource
from sdclientapi import Submission as SDKSubmission
from sqlalchemy import and_, desc, or_
from sqlalchemy.orm.exc import NoResultFound
from sqlalchemy.orm.session import Session

from securedrop_client.db import (
    DraftReply,
    File,
    Message,
    Reply,
    ReplySendStatus,
    ReplySendStatusCodes,
    Source,
    User,
)
from securedrop_client.utils import SourceCache, UserCache, chronometer, memoize

logger = logging.getLogger(__name__)


def get_local_sources(session: Session) -> List[Source]:
    """
    Return all source objects from the local database, newest first.
    """
    return session.query(Source).order_by(desc(Source.last_updated)).all()


def delete_local_source_by_uuid(session: Session, uuid: str, data_dir: str) -> None:
    """
    Delete the source with the referenced UUID.
    """
    source = session.query(Source).filter_by(uuid=uuid).one_or_none()
    if source:
        delete_source_collection(source.journalist_filename, data_dir)
        session.delete(source)
        session.commit()
        logger.info("Deleted source with UUID {} from local database.".format(uuid))


def get_local_messages(session: Session) -> List[Message]:
    """
    Return all submission objects from the local database.
    """
    return session.query(Message).all()


def get_local_files(session: Session) -> List[File]:
    """
    Return all file (a submitted file) objects from the local database.
    """
    return session.query(File).all()


def get_local_replies(session: Session) -> List[Reply]:
    """
    Return all reply objects from the local database that are successful.
    """
    return session.query(Reply).all()


def get_remote_data(api: API) -> Tuple[List[SDKSource], List[SDKSubmission], List[SDKReply]]:
    """
    Given an authenticated connection to the SecureDrop API, get sources,
    submissions and replies from the remote server and return a tuple
    containing lists of objects representing this data:

    (remote_sources, remote_submissions, remote_replies)
    """
    remote_sources = api.get_sources()
    remote_submissions = api.get_all_submissions()
    remote_replies = api.get_all_replies()

    logger.info("Fetched {} remote sources.".format(len(remote_sources)))
    logger.info("Fetched {} remote submissions.".format(len(remote_submissions)))
    logger.info("Fetched {} remote replies.".format(len(remote_replies)))

    return (remote_sources, remote_submissions, remote_replies)


def update_local_storage(
    session: Session,
    remote_sources: List[SDKSource],
    remote_submissions: List[SDKSubmission],
    remote_replies: List[SDKReply],
    data_dir: str,
) -> None:
    """
    Given a database session and collections of remote sources, submissions and
    replies from the SecureDrop API, ensures the local database is updated
    with this data.
    """

    remote_messages = [x for x in remote_submissions if x.filename.endswith("msg.gpg")]
    remote_files = [x for x in remote_submissions if not x.filename.endswith("msg.gpg")]

    # The following update_* functions may change the database state.
    # Because of that, each get_local_* function needs to be called just before
    # its respective update_* function.
    with chronometer(logger, "update_sources"):
        update_sources(remote_sources, get_local_sources(session), session, data_dir)

    with chronometer(logger, "update_files"):
        update_files(remote_files, get_local_files(session), session, data_dir)

    with chronometer(logger, "update_messages"):
        update_messages(remote_messages, get_local_messages(session), session, data_dir)

    with chronometer(logger, "update_replies"):
        update_replies(remote_replies, get_local_replies(session), session, data_dir)


def lazy_setattr(o: Any, a: str, v: Any) -> None:
    """
    Only assign v to o.a if they differ.

    Intended to avoid unnecessarily dirtying SQLAlchemy objects during
    sync.
    """
    if getattr(o, a) != v:
        setattr(o, a, v)


def update_sources(
    remote_sources: List[SDKSource], local_sources: List[Source], session: Session, data_dir: str
) -> None:
    """
    Given collections of remote sources, the current local sources and a
    session to the local database, ensure the state of the local database
    matches that of the remote sources:

    * Existing items are updated in the local database.
    * New items are created in the local database.
    * Local items not returned in the remote sources are deleted from the
      local database.
    """
    local_sources_by_uuid = {s.uuid: s for s in local_sources}
    for source in remote_sources:
        if source.uuid in local_sources_by_uuid:
            # Update an existing record.
            local_source = local_sources_by_uuid[source.uuid]
            lazy_setattr(local_source, "journalist_designation", source.journalist_designation)
            lazy_setattr(local_source, "is_flagged", source.is_flagged)
            lazy_setattr(local_source, "interaction_count", source.interaction_count)
            lazy_setattr(local_source, "document_count", source.number_of_documents)
            lazy_setattr(local_source, "is_starred", source.is_starred)
            lazy_setattr(local_source, "last_updated", parse(source.last_updated))
            lazy_setattr(local_source, "public_key", source.key["public"])
            lazy_setattr(local_source, "fingerprint", source.key["fingerprint"])

            # Removing the UUID from local_sources_by_uuid ensures
            # this record won't be deleted at the end of this
            # function.
            del local_sources_by_uuid[source.uuid]
            logger.debug("Updated source {}".format(source.uuid))
        else:
            # A new source to be added to the database.
            ns = Source(
                uuid=source.uuid,
                journalist_designation=source.journalist_designation,
                is_flagged=source.is_flagged,
                interaction_count=source.interaction_count,
                is_starred=source.is_starred,
                last_updated=parse(source.last_updated),
                document_count=source.number_of_documents,
                public_key=source.key["public"],
                fingerprint=source.key["fingerprint"],
            )
            session.add(ns)

            logger.debug("Added new source {}".format(source.uuid))

    # The uuids remaining in local_uuids do not exist on the remote server, so
    # delete the related records.
    for deleted_source in local_sources_by_uuid.values():
        delete_source_collection(deleted_source.journalist_filename, data_dir)
        session.delete(deleted_source)
        logger.debug("Deleted source {}".format(deleted_source.uuid))

    session.commit()


def update_files(
    remote_submissions: List[SDKSubmission],
    local_submissions: List[File],
    session: Session,
    data_dir: str,
) -> None:
    __update_submissions(File, remote_submissions, local_submissions, session, data_dir)


def update_messages(
    remote_submissions: List[SDKSubmission],
    local_submissions: List[Message],
    session: Session,
    data_dir: str,
) -> None:
    __update_submissions(Message, remote_submissions, local_submissions, session, data_dir)


def __update_submissions(
    model: Union[Type[File], Type[Message]],
    remote_submissions: List[SDKSubmission],
    local_submissions: Union[List[Message], List[File]],
    session: Session,
    data_dir: str,
) -> None:
    """
    The logic for updating files and messages is effectively the same, so this function is somewhat
    overloaded to allow us to do both in a DRY way.

    * Existing submissions are updated in the local database.
    * New submissions have an entry created in the local database.
    * Local submissions not returned in the remote submissions are deleted
      from the local database.
    """
    local_submissions_by_uuid = {s.uuid: s for s in local_submissions}
    source_cache = SourceCache(session)
    for submission in remote_submissions:
        local_submission = local_submissions_by_uuid.get(submission.uuid)
        if local_submission:
            lazy_setattr(local_submission, "size", submission.size)
            lazy_setattr(local_submission, "is_read", submission.is_read)
            lazy_setattr(local_submission, "download_url", submission.download_url)

            # Removing the UUID from local_uuids ensures this record won't be
            # deleted at the end of this function.
            del local_submissions_by_uuid[submission.uuid]
            logger.debug(f"Updated {model.__name__} {submission.uuid}")
        else:
            # A new submission to be added to the database.
            source = source_cache.get(submission.source_uuid)
            if source:
                ns = model(
                    source_id=source.id,
                    uuid=submission.uuid,
                    size=submission.size,
                    filename=submission.filename,
                    download_url=submission.download_url,
                )
                session.add(ns)
                logger.debug(f"Added {model.__name__} {submission.uuid}")

    # The uuids remaining in local_uuids do not exist on the remote server, so
    # delete the related records.
    for deleted_submission in local_submissions_by_uuid.values():
        delete_single_submission_or_reply_on_disk(deleted_submission, data_dir)
        session.delete(deleted_submission)
        logger.debug(f"Deleted {model.__name__} {deleted_submission.uuid}")

    session.commit()


def update_replies(
    remote_replies: List[SDKReply], local_replies: List[Reply], session: Session, data_dir: str
) -> None:
    """
    This method does the following for all replies:
      * Deletes user info if the user who sent the reply was deleted on the server
      * Adds reply to the local database if it's new and adds a user account for the sender if
        one does not exist
      * Deletes reply if it no longer exists on the server (pending or failed replies have not
        reached the server so they will continue to exist locally in a separate table called
        draftreplies)
    """
    local_replies_to_process: Dict[str, Reply] = {reply.uuid: reply for reply in local_replies}
    source_cache = SourceCache(session)
    local_users = session.query(User).all()
    local_user_cache = UserCache(session, local_users)

    for remote_reply in remote_replies:
        key = remote_reply.uuid + ":" + remote_reply.username + ":" + remote_reply.firstname + ":" + remote_reply.lastname
        if key in local_user_cache:
            sender = local_user_cache[key]
        else:
            sender = create_or_update_user(
                remote_reply.journalist_uuid,
                remote_reply.journalist_username,
                remote_reply.journalist_first_name,
                remote_reply.journalist_last_name,
                session,
            )
            local_user_cache[sender.uuid + ":" + sender.username + ":" + sender.firstname + ":" + sender.lastname] = sender

        local_reply = local_replies_to_process.get(remote_reply.uuid)
        if local_reply:
            # Delete reply from dict so later we know which replies do not exist remotely
            del local_replies_to_process[local_reply.uuid]

            # Delete user info from local storage if the journalist was deleted from the server. We
            # can infer that the user was deleted from the server when the sender id of an existing
            # reply no longer matches with the server.
            local_sender = session.query(User).filter_by(id=local_reply.journalist_id).one_or_none()
            if local_sender and local_sender.id != sender.id:
                lazy_setattr(local_sender, "deleted", True)
                logger.debug(f"Deleted user info for sender of reply {local_reply.uuid}")
        else:
            # Create and add new reply
            source = source_cache.get(remote_reply.source_uuid)
            if not source:
                logger.error(f"No source found for reply {remote_reply.uuid}")
                continue
            reply = Reply(
                uuid=remote_reply.uuid,
                journalist_id=sender.id,
                source_id=source.id,
                filename=remote_reply.filename,
                size=remote_reply.size,
            )
            session.add(reply)
            session.commit()
            logger.debug(f"Added new reply {reply.uuid}")

            # If we're creating a new reply then we can delete its corresponding draft reply if one
            # exists. If the new reply was sent from the JI then there will not be a draft reply.
            draft_reply = session.query(DraftReply).filter_by(uuid=remote_reply.uuid).one_or_none()
            if draft_reply:
                update_draft_replies(
                    session,
                    draft_reply.source.id,
                    draft_reply.timestamp,
                    draft_reply.file_counter,
                    reply.file_counter,
                    commit=False,
                )
                session.delete(draft_reply)
                logger.debug("Deleted draft reply {}".format(draft_reply.uuid))

    # Any local replies that still haven't been processed after iterating through all the
    # remote replies means they've been deleted from ther server, do make sure to delete them
    # locally as well
    for local_reply in local_replies_to_process.values():
        delete_single_submission_or_reply_on_disk(local_reply, data_dir)
        session.delete(local_reply)
        logger.debug("Deleted reply {}".format(local_reply.uuid))

    session.commit()


def create_or_update_user(
    uuid: str, username: str, firstname: str, lastname: str, session: Session
) -> User:
    """
    Return a User object with the supplied journalist UUID. Create a new account if no user exists
    in the local database with that UUID, or update the existing user if username, first name, or
    last name have changed.
    """
    user = session.query(User).filter_by(uuid=uuid).one_or_none()

    if not user:
        new_user = User(username=username, firstname=firstname, lastname=lastname)
        new_user.uuid = uuid
        session.add(new_user)
        session.commit()
        return new_user

    if user.username != username:
        user.username = username
        session.commit()
    if user.firstname != firstname:
        user.firstname = firstname
        session.commit()
    if user.lastname != lastname:
        user.lastname = lastname
        session.commit()

    return user


def update_missing_files(data_dir: str, session: Session) -> List[File]:
    """
    Update files that are marked as downloaded yet missing from the filesystem.
    """
    files_that_have_been_downloaded = session.query(File).filter_by(is_downloaded=True).all()
    files_that_are_missing = []
    for f in files_that_have_been_downloaded:
        if not os.path.exists(f.location(data_dir)):
            files_that_are_missing.append(f)
            mark_as_not_downloaded(f.uuid, session)
    return files_that_are_missing


def update_draft_replies(
    session: Session,
    source_id: int,
    timestamp: datetime,
    old_file_counter: int,
    new_file_counter: int,
    commit: bool = True,
) -> None:
    """
    When we confirm a sent reply R, if there are drafts that were sent after it,
    we need to reposition them to ensure that they appear _after_ the confirmed
    replies. We do this by updating the file_counter stored on the drafts sent
    after reply R.

    Example:
        1. Reply Q, has file_counter=2
        2. User adds DraftReply R, it has file_counter=2
        3. User adds DraftReply S, it has file_counter=2 and
           timestamp(S) > timestamp(R).
        4. DraftReply R saved on server with file_counter=4 (this can happen as other
           journalist can be sending replies), it is converted to Reply R locally.
        5. We must now update file_counter on DraftReply S such that it appears
           after Reply R in the conversation view.

    Args:
        session (Session): The SQLAlchemy session object to be used.
        source_id (int): this is the ID of the source that the reply R corresponds to.
        timestamp (datetime): this is the timestamp of the draft that corresponds to
            reply R.
        old_file_counter (int): this is the file_counter of the draft that
            corresponds to reply R.
        new_file_counter (int): this is the file_counter of the reply R confirmed
            as successfully sent from the server.
    """
    for draft_reply in (
        session.query(DraftReply)
        .filter(
            and_(
                DraftReply.source_id == source_id,
                DraftReply.timestamp > timestamp,
                DraftReply.file_counter == old_file_counter,
            )
        )
        .all()
    ):
        draft_reply.file_counter = new_file_counter
        session.add(draft_reply)
    if commit:
        session.commit()


def find_new_files(session: Session) -> List[File]:
    q = session.query(File).join(Source).filter_by(is_downloaded=False)
    q = q.order_by(desc(Source.last_updated))
    return q.all()


def find_new_messages(session: Session) -> List[Message]:
    """
    Find messages to process. Those messages are those where one of the following
    conditions is true:

    * The message has not yet been downloaded.
    * The message has not yet had decryption attempted.
    * Decryption previously failed on a message.
    """
    q = (
        session.query(Message)
        .join(Source)
        .filter(
            or_(
                Message.is_downloaded == False,
                Message.is_decrypted == False,
                Message.is_decrypted == None,
            )
        )
    )  # noqa: E712
    q = q.order_by(desc(Source.last_updated))
    return q.all()


def find_new_replies(session: Session) -> List[Reply]:
    """
    Find replies to process. Those replies are those where one of the following
    conditions is true:

    * The reply has not yet been downloaded.
    * The reply has not yet had decryption attempted.
    * Decryption previously failed on a reply.
    """
    q = (
        session.query(Reply)
        .join(Source)
        .filter(
            or_(
                Reply.is_downloaded == False,
                Reply.is_decrypted == False,
                Reply.is_decrypted == None,
            )
        )
    )  # noqa: E712
    q = q.order_by(desc(Source.last_updated))
    return q.all()


def mark_as_not_downloaded(uuid: str, session: Session) -> None:
    """
    Mark File as not downloaded in the database.
    """
    db_obj = session.query(File).filter_by(uuid=uuid).one()
    db_obj.is_downloaded = False
    db_obj.is_decrypted = None
    session.add(db_obj)
    session.commit()


def mark_as_downloaded(
    model_type: Union[Type[File], Type[Message], Type[Reply]], uuid: str, session: Session
) -> None:
    """
    Mark object as downloaded in the database.
    """
    db_obj = session.query(model_type).filter_by(uuid=uuid).one()
    db_obj.is_downloaded = True
    session.add(db_obj)
    session.commit()


def update_file_size(uuid: str, path: str, session: Session) -> None:
    """
    Updates file size to the decrypted size
    """
    db_obj = session.query(File).filter_by(uuid=uuid).one()
    stat = Path(db_obj.location(path)).stat()
    db_obj.size = stat.st_size
    session.add(db_obj)
    session.commit()


def mark_as_decrypted(
    model_type: Union[Type[File], Type[Message], Type[Reply]],
    uuid: str,
    session: Session,
    is_decrypted: bool = True,
    original_filename: str = None,
) -> None:
    """
    Mark object as downloaded in the database.
    """
    db_obj = session.query(model_type).filter_by(uuid=uuid).one()
    db_obj.is_decrypted = is_decrypted

    if model_type == File and original_filename:
        db_obj.filename = original_filename

    session.add(db_obj)
    session.commit()


def set_message_or_reply_content(
    model_type: Union[Type[Message], Type[Reply]], uuid: str, content: str, session: Session
) -> None:
    """
    Mark whether or not the object is decrypted. If it's not decrypted, do not set content. If the
    object is a File, do not set content (filesystem storage is used instead).
    """
    db_obj = session.query(model_type).filter_by(uuid=uuid).one_or_none()
    db_obj.content = content
    session.add(db_obj)
    session.commit()


def delete_source_collection(journalist_filename: str, data_dir: str) -> None:
    source_folder = os.path.join(data_dir, journalist_filename)
    try:
        shutil.rmtree(source_folder)
        logging.info("Source documents for {} deleted".format(journalist_filename))
    except FileNotFoundError:
        logging.info("No source documents for {} to delete".format(journalist_filename))


def delete_single_submission_or_reply_on_disk(
    obj_db: Union[File, Message, Reply], data_dir: str
) -> None:
    """
    Delete on disk any files associated with a single submission or reply.
    """

    try:
        os.remove(obj_db.location(data_dir))
    except FileNotFoundError:
        logging.info("Object %s already deleted, skipping", obj_db.location(data_dir))

    if isinstance(obj_db, File):
        # Also delete the file's enclosing folder.
        try:
            shutil.rmtree(os.path.dirname(obj_db.location(data_dir)))
        except FileNotFoundError:
            pass


def source_exists(session: Session, source_uuid: str) -> bool:
    try:
        session.query(Source).filter_by(uuid=source_uuid).one()
        return True
    except NoResultFound:
        return False


def get_file(session: Session, uuid: str) -> File:
    return session.query(File).filter_by(uuid=uuid).one()


def get_message(session: Session, uuid: str) -> Message:
    return session.query(Message).filter_by(uuid=uuid).one()


def get_reply(session: Session, uuid: str) -> Reply:
    return session.query(Reply).filter_by(uuid=uuid).one()


def mark_all_pending_drafts_as_failed(session: Session) -> List[DraftReply]:
    """
    When we login (offline or online) or logout, we need to set all the pending replies as failed.
    """
    pending_status = (
        session.query(ReplySendStatus).filter_by(name=ReplySendStatusCodes.PENDING.value).one()
    )
    failed_status = (
        session.query(ReplySendStatus).filter_by(name=ReplySendStatusCodes.FAILED.value).one()
    )

    pending_drafts = session.query(DraftReply).filter_by(send_status=pending_status).all()
    for pending_draft in pending_drafts:
        pending_draft.send_status = failed_status

    session.commit()

    return pending_drafts


def clear_download_errors(session: Session) -> None:
    """
    Clears all File, Message, or Reply download errors.
    """
    session.execute("""UPDATE files SET download_error_id = null;""")
    session.execute("""UPDATE messages SET download_error_id = null;""")
    session.execute("""UPDATE replies SET download_error_id = null;""")
    session.commit()
