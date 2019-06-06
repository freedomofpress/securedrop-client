import binascii
import hashlib
import logging
import os
import sdclientapi
import shutil
from tempfile import NamedTemporaryFile
from typing import Any, Union, Type, Tuple

from sdclientapi import API
from sqlalchemy.orm.session import Session

from securedrop_client.api_jobs.base import ApiJob
from securedrop_client.crypto import GpgHelper, CryptoError
from securedrop_client.db import File, Message, Reply
from securedrop_client.storage import mark_message_as_downloaded, mark_file_as_downloaded, \
    set_object_decryption_status_with_content

logger = logging.getLogger(__name__)


class MessageDownloadJob(ApiJob):

    def __init__(self, uuid: str, download_dir: str, gpg: GpgHelper) -> None:
        super().__init__()
        self.download_dir = download_dir
        self.type = Message
        self.uuid = uuid
        self.gpg = gpg

    def call_api(self, api_client: API, session: Session) -> Any:
        # Download
        db_object = session.query(self.type).filter_by(uuid=self.uuid).one()
        if not db_object.is_downloaded:
            _, filepath = self._make_call(db_object, api_client)
            mark_message_as_downloaded(db_object.uuid, session)
        else:
            filepath = os.path.join(self.download_dir, db_object.filename)

        # Decrypt
        self._decrypt_file(session, db_object, filepath)

        return db_object.uuid

    def _make_call(self, db_object: Message, api_client: API) -> Tuple[str, str]:
        sdk_obj = sdclientapi.Submission(uuid=db_object.uuid)
        sdk_obj.filename = db_object.filename
        sdk_obj.source_uuid = db_object.source.uuid

        return api_client.download_submission(sdk_obj)

    def _decrypt_file(
        self,
        session: Session,
        encrypted_file: Union[File, Message, Reply],
        filepath: str,
    ) -> None:
        with NamedTemporaryFile('w+') as plaintext_file:
            try:
                self.gpg.decrypt_submission_or_reply(filepath, plaintext_file.name, False)
                plaintext_file.seek(0)
                content = plaintext_file.read()
                set_object_decryption_status_with_content(encrypted_file, session, True, content)
                logger.info("File decrypted: {}".format(encrypted_file.filename))
            except CryptoError:
                set_object_decryption_status_with_content(encrypted_file, session, False)
                logger.info("Failed to decrypt file: {}".format(encrypted_file.filename))


class FileDownloadJob(ApiJob):

    CHUNK_SIZE = 4096

    def __init__(
        self,
        submission_type: Union[Type[File], Type[Message]],
        submission_uuid: str,
        data_dir: str,
        gpg: GpgHelper,
    ) -> None:
        super().__init__()
        self.data_dir = data_dir
        self.submission_type = submission_type
        self.submission_uuid = submission_uuid
        self.gpg = gpg

    def call_api(self, api_client: API, session: Session) -> Any:
        db_object = session.query(self.submission_type) \
            .filter_by(uuid=self.submission_uuid).one()

        etag, download_path = self._make_call(db_object, api_client)

        if not self._check_file_integrity(etag, download_path):
            raise RuntimeError('Downloaded file had an invalid checksum.')

        self._decrypt_file(session, db_object, download_path)

        return db_object.uuid

    def _make_call(self, db_object: Union[File, Message], api_client: API) -> Tuple[str, str]:
        sdk_obj = sdclientapi.Submission(uuid=db_object.uuid)
        sdk_obj.filename = db_object.filename
        sdk_obj.source_uuid = db_object.source.uuid

        return api_client.download_submission(sdk_obj)

    @classmethod
    def _check_file_integrity(cls, etag: str, file_path: str) -> bool:
        '''
        Checks if the file is valid.
        :return: `True` if valid or unknown, `False` otherwise.
        '''
        if not etag:
            logger.debug('No ETag. Skipping integrity check for file at {}'.format(file_path))
            return True

        alg, checksum = etag.split(':')

        if alg == 'sha256':
            hasher = hashlib.sha256()
        else:
            logger.debug('Unknown hash algorithm ({}). Skipping integrity check for file at {}'
                         .format(alg, file_path))
            return True

        with open(file_path, 'rb') as f:
            while True:
                read_bytes = f.read(cls.CHUNK_SIZE)
                if not read_bytes:
                    break
                hasher.update(read_bytes)

        calculated_checksum = binascii.hexlify(hasher.digest()).decode('utf-8')
        return calculated_checksum == checksum

    def _decrypt_file(
        self,
        session: Session,
        db_object: Union[File, Message],
        file_path: str,
    ) -> None:
        file_uuid = db_object.uuid
        server_filename = db_object.filename

        # The filename contains the location where the file has been stored. On non-Qubes OSes, this
        # will be the data directory. On Qubes OS, this will a ~/QubesIncoming directory. In case we
        # are on Qubes, we should move the file to the data directory and name it the same as the
        # server (e.g. spotless-tater-msg.gpg).
        filepath_in_datadir = os.path.join(self.data_dir, server_filename)
        shutil.move(file_path, filepath_in_datadir)
        mark_file_as_downloaded(file_uuid, session)

        try:
            self.gpg.decrypt_submission_or_reply(filepath_in_datadir, server_filename, is_doc=True)
        except CryptoError as e:
            logger.debug('Failed to decrypt file {}: {}'.format(server_filename, e))
            set_object_decryption_status_with_content(db_object, session, False)
            raise e

        set_object_decryption_status_with_content(db_object, session, True)
