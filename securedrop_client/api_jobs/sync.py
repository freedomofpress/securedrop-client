import binascii
import hashlib
import logging
import os
import sdclientapi
import shutil
from tempfile import NamedTemporaryFile
from typing import List, Tuple, Type, Union

from sdclientapi import API
from sdclientapi import Source as SDKSource
from sdclientapi import Submission as SDKSubmission
from sdclientapi import Reply as SDKReply
from sqlalchemy.orm.session import Session

from securedrop_client import storage
from securedrop_client.api_jobs.base import ApiJob
from securedrop_client.crypto import GpgHelper, CryptoError
from securedrop_client.db import File, Message, Reply


logger = logging.getLogger(__name__)


class SyncJob(ApiJob):

    CHUNK_SIZE = 4096

    def __init__(self, gpg: GpgHelper, data_dir: str) -> None:
        super().__init__()
        self.gpg = gpg
        self.data_dir = data_dir

    def call_api(self, api_client: API, session: Session) -> None:
        # Get remote data
        remote_sources, remote_submissions, remote_replies = self._make_call(api_client)

        logger.info('Fetched {} remote sources.'.format(len(remote_sources)))
        logger.info('Fetched {} remote submissions.'.format(len(remote_submissions)))
        logger.info('Fetched {} remote replies.'.format(len(remote_replies)))

        # Update database
        storage.update_local_storage(session,
                                     remote_sources,
                                     remote_submissions,
                                     remote_replies,
                                     self.data_dir)
        # Decrypt
        for submission in remote_submissions:
            _, filepath = api_client.download_submission(submission)
            db_submission = session.query(Message).filter_by(uuid=submission.uuid).one_or_none()
            storage.mark_message_as_downloaded(db_submission.uuid, session)
            self._decrypt_the_thing(session, filepath, db_submission)
        for reply in remote_replies:
            _, filepath = api_client.download_reply(reply)
            db_reply = session.query(Reply).filter_by(uuid=reply.uuid).one_or_none()
            storage.mark_reply_as_downloaded(db_reply.uuid, session)
            self._decrypt_the_thing(session, filepath, db_reply)

        # import keys into keyring
        for source in remote_sources:
            if source.key and source.key.get('type', None) == 'PGP':
                pub_key = source.key.get('public', None)
                fingerprint = source.key.get('fingerprint', None)
                if not pub_key or not fingerprint:
                    continue
                try:
                    self.gpg.import_key(source.uuid, pub_key, fingerprint)
                except CryptoError:
                    logger.warning('Failed to import key for source {}'.format(source.uuid))

    def _make_call(self, api: API) -> Tuple[List[SDKSource], List[SDKSubmission], List[SDKReply]]:
        """
        Given an authenticated connection to the SecureDrop API, get sources,
        submissions and replies from the remote server and return a tuple
        containing lists of objects representing this data:

        (remote_sources, remote_submissions, remote_replies)
        """
        remote_sources = api.get_sources()
        remote_submissions = []
        for source in remote_sources:
            remote_submissions.extend(api.get_submissions(source))
        remote_replies = api.get_all_replies()

        return (remote_sources, remote_submissions, remote_replies)

    def _decrypt_the_thing(
        self,
        session: Session,
        filepath: str,
        thing: Union[File, Message, Reply],
    ) -> None:

        with NamedTemporaryFile('w+') as plaintext_file:
            try:
                self.gpg.decrypt_submission_or_reply(filepath, plaintext_file.name, False)
                plaintext_file.seek(0)
                content = plaintext_file.read()
                storage.set_object_decryption_status_with_content(thing, session, True, content)
                logger.info("Message or reply decrypted: {}".format(thing.filename))
            except CryptoError:
                storage.set_object_decryption_status_with_content(thing, session, False)
                logger.info("Message or reply failed to decrypt: {}".format(thing.filename))