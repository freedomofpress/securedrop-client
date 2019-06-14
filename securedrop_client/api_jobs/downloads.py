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
from securedrop_client.storage import mark_as_downloaded, set_decryption_status_with_content

logger = logging.getLogger(__name__)


class MessageDownloadJob(ApiJob):
    '''
    Download and decrypt a message from a source.
    '''
    def __init__(self, uuid: str, data_dir: str, gpg: GpgHelper) -> None:
        super().__init__()
        self.uuid = uuid
        self.data_dir = data_dir
        self.gpg = gpg
        self.db_model_type = Message

    def call_api(self, api_client: API, session: Session) -> Any:
        '''
        Download and decrypt.
        '''
        db_object = session.query(self.db_model_type).filter_by(uuid=self.uuid).one()

        if db_object.is_decrypted:
            return db_object.uuid

        if db_object.is_downloaded:
            self._decrypt_file(session, db_object, os.path.join(self.data_dir, db_object.filename))
            return db_object.uuid

        self._download(api_client, db_object, session)
        self._decrypt_file(session, db_object, os.path.join(self.data_dir, db_object.filename))
        return db_object.uuid

    def _download(self, api: API, db_object: Message, session: Session) -> None:
        '''
        Download the file. Check file integrity and move it to the data directory before marking it
        as downloaded.

        Note: On Qubes OS, files are downloaded to ~/QubesIncoming.
        '''
        etag, download_path = self._make_call(db_object, api)

        shutil.move(download_path, os.path.join(self.data_dir, db_object.filename))
        mark_as_downloaded(type(db_object), db_object.uuid, session)

    def _make_call(self, db_object: Message, api_client: API) -> Tuple[str, str]:
        sdk_obj = sdclientapi.Submission(uuid=db_object.uuid)
        sdk_obj.filename = db_object.filename
        sdk_obj.source_uuid = db_object.source.uuid
        return api_client.download_submission(sdk_obj)

    def _decrypt_file(
        self,
        session: Session,
        db_object: Union[File, Message, Reply],
        filepath: str,
    ) -> None:
        '''
        Decrypt file and store its plaintext content.

        If the plaintext content is a message or a reply, store it in the local database, otherwise
        store the document in the filesystem.
        '''
        try:
            # Store plaintext in a temporary file that will be deleted when the file closes. It's
            # needed just long enough to store the plaintext in the local db.
            plaintextfile = NamedTemporaryFile('w+')

            self.gpg.decrypt_submission_or_reply(
                filepath,
                plaintextfile.name,
                is_doc=False)

            plaintext = open(plaintextfile.name).read()
            set_decryption_status_with_content(
                model_type=type(db_object),
                uuid=db_object.uuid,
                is_decrypted=True,
                session=session,
                content=plaintext)

            logger.info("File decrypted: {}".format(db_object.filename))
        except CryptoError:
            set_decryption_status_with_content(
                model_type=type(db_object),
                uuid=db_object.uuid,
                is_decrypted=False,
                session=session)

            logger.info("Failed to decrypt file: {}".format(db_object.filename))


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
        '''
        Download and decrypt.
        '''
        db_object = session.query(self.submission_type).filter_by(uuid=self.submission_uuid).one()

        if db_object.is_decrypted:
            return db_object.uuid

        if db_object.is_downloaded:
            self._decrypt_file(session, db_object, os.path.join(self.data_dir, db_object.filename))
            return db_object.uuid

        self._download(api_client, db_object, session)
        self._decrypt_file(session, db_object, os.path.join(self.data_dir, db_object.filename))
        return db_object.uuid

    def _download(self, api_client: API, db_object: File, session: Session) -> None:
        '''
        Download the file. Check file integrity and move it to the data directory before marking it
        as downloaded.

        Note: On Qubes OS, files are downloaded to ~/QubesIncoming.
        '''
        etag, download_path = self._make_call(db_object, api_client)

        if not self._check_file_integrity(etag, download_path):
            raise RuntimeError('Downloaded file had an invalid checksum.')

        data_path = os.path.join(self.data_dir, db_object.filename)
        shutil.move(download_path, data_path)

        mark_as_downloaded(type(db_object), db_object.uuid, session)

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
        db_object: Union[File, Message, Reply],
        filepath: str,
    ) -> None:
        '''
        If a File: decrypt and save plaintext to a file on the filesystem.
        If a Message or Reply: decrypt and save plaintext to local database.
        '''
        try:
            # Store plaintext in a file named after the downloaded file name, but without the
            # extensions, e.g. 1-impractical_thing-doc.gz.gpg -> 1-impractical_thing-doc
            fn_no_ext, _ = os.path.splitext(os.path.splitext(os.path.basename(filepath))[0])
            plaintext_filepath = os.path.join(self.data_dir, fn_no_ext)

            self.gpg.decrypt_submission_or_reply(
                filepath,
                plaintext_filepath,
                is_doc=True)

            set_decryption_status_with_content(
                model_type=type(db_object),
                uuid=db_object.uuid,
                is_decrypted=True,
                session=session)

            logger.debug("File decrypted: {}".format(db_object.filename))
        except CryptoError as e:
            set_decryption_status_with_content(
                model_type=type(db_object),
                uuid=db_object.uuid,
                is_decrypted=False,
                session=session)

            logger.debug("Failed to decrypt file: {}".format(db_object.filename))

            raise e
