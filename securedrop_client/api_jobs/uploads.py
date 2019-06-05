import logging
import sdclientapi
import traceback

from sdclientapi import API
from sqlalchemy.orm.session import Session

from securedrop_client.api_jobs.base import ApiJob
from securedrop_client.crypto import GpgHelper
from securedrop_client.db import Reply, Source

logger = logging.getLogger(__name__)


class SendReplyJob(ApiJob):
    def __init__(
        self,
        source_uuid: str,
        reply_uuid: str,
        message: str,
        gpg: GpgHelper,
    ) -> None:
        super().__init__()
        self.source_uuid = source_uuid
        self.reply_uuid = reply_uuid
        self.message = message
        self.gpg = gpg

    def call_api(self, api_client: API, session: Session) -> str:
        try:
            encrypted_reply = self.gpg.encrypt_to_source(self.source_uuid,
                                                         self.message)
        except Exception:
            tb = traceback.format_exc()
            logger.error('Failed to encrypt to source {}:\n'.format(
                self.source_uuid, tb))
            # We raise the exception as it will get handled in ApiJob._do_call_api
            # Exceptions must be raised for the failure signal to be emitted.
            raise
        else:
            sdk_reply = self._make_call(encrypted_reply, api_client)

        # Now that the call was successful, add the reply to the database locally.
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

    def _make_call(self, encrypted_reply: str, api_client: API) -> sdclientapi.Reply:
        sdk_source = sdclientapi.Source(uuid=self.source_uuid)
        return api_client.reply_source(sdk_source, encrypted_reply,
                                       self.reply_uuid)
