import logging
import os

import sdclientapi
from sdclientapi import API, RequestTimeoutError, ServerConnectionError
from sqlalchemy.exc import SQLAlchemyError
from sqlalchemy.orm.session import Session

from securedrop_client.api_jobs.base import SingleObjectApiJob
from securedrop_client.crypto import GpgHelper
from securedrop_client.db import (
    Reply,
    Source,
    User,
)
from securedrop_client.storage import update_draft_replies

logger = logging.getLogger(__name__)


class SendReplyJob(SingleObjectApiJob):
    def __init__(self, source_uuid: str, reply_uuid: str, message: str, gpg: GpgHelper) -> None:
        super().__init__(reply_uuid)
        self.source_uuid = source_uuid
        self.reply_uuid = reply_uuid
        self.message = message
        self.gpg = gpg

    def call_api(self, api_client: API, session: Session) -> str:
        """
        Override ApiJob.

        Encrypt the reply and send it to the server. If the call is successful,
        update the local Reply and return its UUID. Otherwise raise a
        SendReplyJobException with the UUID.
        """

        try:
            reply = session.query(Reply).filter_by(uuid=self.reply_uuid).one_or_none()

            # If `reply` was deleted locally, then do not send the message to
            # the source.
            if not reply:
                raise Exception("Reply {} does not exist".format(self.reply_uuid))

            # If `reply` made it to the server, but we didn't get a 201
            # response back, we might have already fetched it successfully.
            if reply.state == Reply.READY:
                logger.debug("Reply {} has already been sent successfully".format(self.reply_uuid))
                return reply.uuid

            # If the sender's account no longer exists, then do not send `reply`.  Raising an
            # exception here will mark (and display) it as failed.
            sender = (
                session.query(User).filter_by(uuid=api_client.token_journalist_uuid).one_or_none()
            )
            if not sender:
                raise Exception("Sender of reply {} has been deleted".format(self.reply_uuid))

            # Send the draft reply to the source
            reply.sending()
            session.commit()
            encrypted_reply = self.gpg.encrypt_to_source(self.source_uuid, self.message)
            sdk_reply = self._make_call(encrypted_reply, api_client)

            # Update the reply object
            reply.filename = sdk_reply.filename
            reply.file_counter = int(reply.filename.split("-")[0])
            reply.sent()

            # Update the source and the rest of its pending replies:
            reply.source.interaction_count = reply.file_counter
            session.add(reply.source)

            update_draft_replies(
                session,
                reply.source.id,
                reply.file_counter,
                commit=False,
            )

            session.commit()

            return reply.uuid
        except (RequestTimeoutError, ServerConnectionError) as e:
            message = "Failed to send reply for source {id} due to Exception: {error}".format(
                id=self.source_uuid, error=e
            )
            raise SendReplyJobTimeoutError(message, self.reply_uuid)
        except Exception as e:
            # Continue to store the draft reply
            message = """
                Failed to send reply {uuid} for source {id} due to Exception: {error}
            """.format(
                uuid=self.reply_uuid, id=self.source_uuid, error=e
            )
            self._set_status_to_failed(session)
            raise SendReplyJobError(message, self.reply_uuid)

    def _set_status_to_failed(self, session: Session) -> None:
        try:  # If draft exists, we set it to failed.
            reply = session.query(Reply).filter_by(uuid=self.reply_uuid).one()
            reply.send_failed()
            session.commit()
        except SQLAlchemyError as e:
            logger.info(f"SQL error when setting reply {self.reply_uuid} as failed, skipping")
            logger.debug(f"SQL error when setting reply {self.reply_uuid} as failed, skipping: {e}")
        except Exception as e:
            logger.error(f"Unknown error when setting reply {self.reply_uuid} as failed, skipping")
            logger.debug(
                f"Unknown error when setting reply {self.reply_uuid} as failed, skipping: {e}"
            )

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
