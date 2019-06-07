import binascii
import hashlib
import logging
import os
import sdclientapi
from tempfile import NamedTemporaryFile
from typing import Any, Union, Type

from sdclientapi import API, BaseError
from sdclientapi import Submission as SdkSubmission
from sqlalchemy.orm.session import Session

from securedrop_client.api_jobs.base import ApiJob
from securedrop_client.crypto import GpgHelper, CryptoError
from securedrop_client.db import File, Message
from securedrop_client.storage import mark_message_as_downloaded, mark_file_as_downloaded, \
    set_object_decryption_status_with_content

logger = logging.getLogger(__name__)


class DownloadJob(ApiJob):

    def __init__(self,
                 gpg: GpgHelper,
                 uuid: str,
                 file_type: Union[Type[File], Type[Message]],
                 download_dir: str) -> None:

        super().__init__()
        self.gpg = gpg
        self.uuid = uuid
        self.file_type = file_type
        self.is_doc = True if self.file_type is File else False
        self.download_dir = download_dir

    def call_api_download(self, api: API, sdk_object: SdkSubmission, session: Session) -> str:
        '''
        Method for making the actual download API call and handling the result. Must return the path
        of the downloaded file.
        '''
        raise NotImplementedError

    def call_api(self, api_client: API, session: Session) -> Any:
        '''
        Downloads the file by ultimately calling the `call_api_download` method and decrypts it.
        '''
        db_object = session.query(self.file_type).filter_by(uuid=self.uuid).one()
        filepath = self._download_file(db_object, api_client, session)
        self._decrypt_file(filepath, db_object, session)
        return db_object.uuid

    def _download_file(self, db_object: Union[Message, File], api: API, session: Session) -> str:
        '''
        Download the file and return its path.
        '''
        if db_object.is_downloaded:
            logger.debug("Already downloaded {}".format(db_object.filename))
            return os.path.join(self.download_dir, db_object.filename)

        try:
            sdk_object = sdclientapi.Submission(uuid=db_object.uuid)
            sdk_object.filename = db_object.filename
            sdk_object.source_uuid = db_object.source.uuid
            return self.call_api_download(api, sdk_object, session)
        except BaseError as e:
            logger.debug('Failed to download {}: {}'.format(db_object.filename, e))
            raise e

    def _decrypt_file(self,
                      filepath: str,
                      db_object: Union[Message, File],
                      session: Session) -> None:
        '''
        Decrypt the file specified by filepath
        '''
        if db_object.is_decrypted:
            logger.debug("Already decrypted {}".format(db_object.filename))
            return

        with NamedTemporaryFile('w+') as plaintext_file:
            try:
                self.gpg.decrypt_submission_or_reply(filepath, plaintext_file.name, self.is_doc)
                plaintext_file.seek(0)
                content = plaintext_file.read()
                set_object_decryption_status_with_content(db_object, session, True, content)
                logger.debug("Decrypted {}".format(db_object.filename))
            except CryptoError as e:
                set_object_decryption_status_with_content(db_object, session, False)
                logger.debug('Failed to decrypt {}: {}'.format(db_object.filename, e))
                raise e


class MessageDownloadJob(DownloadJob):

    def __init__(self, uuid: str, download_dir: str, gpg: GpgHelper) -> None:
        super().__init__(gpg, uuid, Message, download_dir)

    def call_api_download(self, api: API, sdk_object: SdkSubmission, session: Session) -> str:
        etag, filepath = api.download_submission(sdk_object)
        mark_message_as_downloaded(sdk_object.uuid, session)
        logger.debug("Downloaded {}".format(sdk_object.filename))
        return filepath


class FileDownloadJob(DownloadJob):

    CHUNK_SIZE = 4096

    def __init__(self, uuid: str, download_dir: str, gpg: GpgHelper) -> None:
        super().__init__(gpg, uuid, File, download_dir)

    def call_api_download(self, api: API, sdk_object: SdkSubmission, session: Session) -> str:
        etag, filepath = api.download_submission(sdk_object)
        mark_file_as_downloaded(sdk_object.uuid, session)
        logger.debug("Downloaded {}".format(sdk_object.filename))
        self._check_file_integrity(etag, filepath)
        return filepath

    @classmethod
    def _check_file_integrity(cls, etag: str, file_path: str) -> None:
        '''
        Check if the file is valid and raise runtime error if the sha256 checksums do not match.
        '''
        if not etag:
            logger.debug('No ETag. Skipping integrity check for file at {}'.format(file_path))
            return

        alg, checksum = etag.split(':')
        if alg != 'sha256':
            logger.debug('Unknown hash algorithm ({}). Skipping integrity check for file at {}'
                         .format(alg, file_path))
            return

        hasher = hashlib.sha256()
        with open(file_path, 'rb') as f:
            while True:
                read_bytes = f.read(cls.CHUNK_SIZE)
                if not read_bytes:
                    break
                hasher.update(read_bytes)

        calculated_checksum = binascii.hexlify(hasher.digest()).decode('utf-8')
        if calculated_checksum != checksum:
            raise RuntimeError('Downloaded file has an invalid checksum.')
