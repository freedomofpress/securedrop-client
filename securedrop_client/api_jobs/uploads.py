import logging
import sdclientapi

from sdclientapi import API, RequestTimeoutError
from sqlalchemy.orm.session import Session

from securedrop_client.api_jobs.base import ApiJob
from securedrop_client.crypto import GpgHelper
from securedrop_client.db import Reply, Source

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
            encrypted_reply = self.gpg.encrypt_to_source(self.source_uuid, self.message)
            sdk_reply = self._make_call(encrypted_reply, api_client)
            source = session.query(Source).filter_by(uuid=self.source_uuid).one()
            reply_db_object = Reply(
                uuid=self.reply_uuid,
                source_id=source.id,
                journalist_id=api_client.token_journalist_uuid,
                filename=sdk_reply.filename,
                content=self.message,
                is_downloaded=True,
                is_decrypted=True
            )
            session.add(reply_db_object)
            session.commit()
            return reply_db_object.uuid
        except RequestTimeoutError as e:
            message = "Failed to send reply for source {id} due to Exception: {error}".format(
                id=self.source_uuid, error=e)
            raise SendReplyJobTimeoutError(message, self.reply_uuid)
        except Exception as e:
            message = "Failed to send reply for source {id} due to Exception: {error}".format(
                id=self.source_uuid, error=e)
            raise SendReplyJobError(message, self.reply_uuid)

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
