import logging
import sdclientapi

from sdclientapi import API, RequestTimeoutError, ServerConnectionError
from sqlalchemy.orm.session import Session
from sqlalchemy.exc import SQLAlchemyError

from securedrop_client.api_jobs.base import ApiJob
from securedrop_client.crypto import GpgHelper
from securedrop_client.db import DraftReply, Reply, ReplySendStatus, ReplySendStatusCodes, Source
from securedrop_client.storage import update_draft_replies

logger = logging.getLogger(__name__)


class SendReplyJob(ApiJob):
    def __init__(self, source_uuid: str, reply_uuid: str, message: str, gpg: GpgHelper) -> None:
        super().__init__()
        self.source_uuid = source_uuid
        self.reply_uuid = reply_uuid
        self.message = message
        self.gpg = gpg

    def call_api(self, api_client: API, session: Session) -> str:
        '''
        Override ApiJob.

        Encrypt the reply and send it to the server. If the call is successful, add it to the local
        database and return the reply uuid string. Otherwise raise a SendReplyJobException so that
        we can return the reply uuid.
        '''

        try:
            # If the reply has already made it to the server but we didn't get a 201 response back,
            # then a reply with self.reply_uuid will exist in the replies table.
            reply_db_object = session.query(Reply).filter_by(uuid=self.reply_uuid).one_or_none()
            if reply_db_object:
                logger.debug('Reply {} has already been sent successfully'.format(self.reply_uuid))
                return reply_db_object.uuid

            # If the draft does not exist because it was deleted locally then do not send the
            # message to the source.
            draft_reply_db_object = session.query(DraftReply).filter_by(
                uuid=self.reply_uuid).one_or_none()
            if not draft_reply_db_object:
                raise Exception('Draft reply {} does not exist'.format(self.reply_uuid))

            # If the source was deleted locally then do not send the message and delete the draft.
            source = session.query(Source).filter_by(uuid=self.source_uuid).one_or_none()
            if not source:
                session.delete(draft_reply_db_object)
                session.commit()
                raise Exception('Source {} does not exists'.format(self.source_uuid))

            # Send the draft reply to the source
            encrypted_reply = self.gpg.encrypt_to_source(self.source_uuid, self.message)
            sdk_reply = self._make_call(encrypted_reply, api_client)

            # Create a new reply object with an updated filename and file counter
            interaction_count = source.interaction_count + 1
            filename = '{}-{}-reply.gpg'.format(interaction_count, source.journalist_designation)
            reply_db_object = Reply(
                uuid=self.reply_uuid,
                source_id=source.id,
                filename=filename,
                journalist_id=api_client.token_journalist_uuid,
                content=self.message,
                is_downloaded=True,
                is_decrypted=True)
            new_file_counter = int(sdk_reply.filename.split('-')[0])
            reply_db_object.file_counter = new_file_counter
            reply_db_object.filename = sdk_reply.filename

            # Update following draft replies for the same source to reflect the new reply count
            draft_file_counter = draft_reply_db_object.file_counter
            draft_timestamp = draft_reply_db_object.timestamp
            update_draft_replies(
                session, source.id, draft_timestamp, draft_file_counter, new_file_counter,
                commit=False
            )

            # Add reply to replies table and increase the source interaction count by 1 and delete
            # the draft reply.
            session.add(reply_db_object)
            source.interaction_count += 1
            session.add(source)
            session.delete(draft_reply_db_object)
            session.commit()

            return reply_db_object.uuid
        except (RequestTimeoutError, ServerConnectionError) as e:
            message = "Failed to send reply for source {id} due to Exception: {error}".format(
                id=self.source_uuid, error=e)
            raise SendReplyJobTimeoutError(message, self.reply_uuid)
        except Exception as e:
            # Continue to store the draft reply
            message = '''
                Failed to send reply {uuid} for source {id} due to Exception: {error}
            '''.format(uuid=self.reply_uuid, id=self.source_uuid, error=e)
            self._set_status_to_failed(session)
            raise SendReplyJobError(message, self.reply_uuid)

    def _set_status_to_failed(self, session: Session) -> None:
        try:  # If draft exists, we set it to failed.
            draft_reply_db_object = session.query(DraftReply).filter_by(uuid=self.reply_uuid).one()
            reply_status = session.query(ReplySendStatus).filter_by(
                name=ReplySendStatusCodes.FAILED.value).one()
            draft_reply_db_object.send_status_id = reply_status.id
            session.add(draft_reply_db_object)
            session.commit()
        except SQLAlchemyError as e:
            logger.info('SQL error when setting reply {uuid} as failed, skipping: {e}'.format(
                uuid=self.reply_uuid, e=e))
        except Exception as e:
            logger.error('Unknown error when setting reply {uuid} as failed, skipping: {e}'.format(
                uuid=self.reply_uuid, e=e))

    def _make_call(self, encrypted_reply: str, api_client: API) -> sdclientapi.Reply:
        sdk_source = sdclientapi.Source(uuid=self.source_uuid)
        return api_client.reply_source(sdk_source, encrypted_reply, self.reply_uuid)


class SendReplyJobError(Exception):
    def __init__(self, message: str, reply_uuid: str):
        super().__init__(message)
        self.reply_uuid = reply_uuid


class SendReplyJobTimeoutError(RequestTimeoutError):
    def __init__(self, message: str, reply_uuid: str) -> None:
        super().__init__()
        self.reply_uuid = reply_uuid
        self.message = message

    def __str__(self) -> str:
        return self.message
