import binascii
import hashlib
import logging
import os
import shutil

from tempfile import NamedTemporaryFile
from typing import Any, Union, Tuple

from sdclientapi import API, BaseError
from sdclientapi import Reply as SdkReply
from sdclientapi import Submission as SdkSubmission
from sqlalchemy.orm.session import Session

from securedrop_client.api_jobs.base import ApiJob
from securedrop_client.crypto import GpgHelper, CryptoError
from securedrop_client.db import File, Message, Reply
from securedrop_client.storage import mark_as_decrypted, mark_as_downloaded, \
    set_message_or_reply_content

logger = logging.getLogger(__name__)


class DownloadJob(ApiJob):
    '''
    Download and decrypt a file that contains either a message, reply, or file submission.
    '''

    CHUNK_SIZE = 4096

    def __init__(self, data_dir: str) -> None:
        super().__init__()
        self.data_dir = data_dir

    def call_download_api(self, api: API, db_object: Union[File, Message]) -> Tuple[str, str]:
        '''
        Method for making the actual API call to downlod the file and handling the result.

        This MUST return the (etag, filepath) tuple response from the server and MUST raise an
        exception if and only if the download fails.
        '''
        raise NotImplementedError

    def call_decrypt(self, filepath: str, session: Session = None) -> None:
        '''
        Method for decrypting the file and storing the plaintext result.

        This MUST raise an exception if and only if the decryption fails.
        '''
        raise NotImplementedError

    def get_db_object(self, session: Session) -> Union[File, Message]:
        '''
        Get the database object associated with this job.
        '''
        raise NotImplementedError

    def call_api(self, api_client: API, session: Session) -> Any:
        '''
        Download and decrypt the file associated with the database object.
        '''
        db_object = self.get_db_object(session)

        if db_object.is_decrypted:
            return db_object.uuid

        if db_object.is_downloaded:
            self._decrypt(os.path.join(self.data_dir, db_object.filename), db_object, session)
            return db_object.uuid

        self._download(api_client, db_object, session)
        self._decrypt(os.path.join(self.data_dir, db_object.filename), db_object, session)
        return db_object.uuid

    def _download(self,
                  api: API,
                  db_object: Union[File, Message, Reply],
                  session: Session) -> None:
        '''
        Download the encrypted file. Check file integrity and move it to the data directory before
        marking it as downloaded.

        Note: On Qubes OS, files are downloaded to ~/QubesIncoming.
        '''
        try:
            etag, download_path = self.call_download_api(api, db_object)

            if not self._check_file_integrity(etag, download_path):
                raise RuntimeError('Downloaded file had an invalid checksum.')

            shutil.move(download_path, os.path.join(self.data_dir, db_object.filename))
            mark_as_downloaded(type(db_object), db_object.uuid, session)
            logger.info("File downloaded: {}".format(db_object.filename))
        except BaseError as e:
            logger.debug("Failed to download file: {}".format(db_object.filename))
            raise e

    def _decrypt(self,
                 filepath: str,
                 db_object: Union[File, Message, Reply],
                 session: Session) -> None:
        '''
        Decrypt the file located at the given filepath and mark it as decrypted.
        '''
        try:
            self.call_decrypt(filepath, session)
            mark_as_decrypted(type(db_object), db_object.uuid, session)
            logger.info("File decrypted: {}".format(os.path.basename(filepath)))
        except CryptoError as e:
            mark_as_decrypted(type(db_object), db_object.uuid, session, is_decrypted=False)
            logger.debug("Failed to decrypt file: {}".format(os.path.basename(filepath)))
            raise e

    @classmethod
    def _check_file_integrity(cls, etag: str, file_path: str) -> bool:
        '''
        Return True if file checksum is valid or unknown, otherwise return False.
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


class ReplyDownloadJob(DownloadJob):
    '''
    Download and decrypt a reply from a source.
    '''

    def __init__(self, uuid: str, data_dir: str, gpg: GpgHelper) -> None:
        super().__init__(data_dir)
        self.uuid = uuid
        self.gpg = gpg

    def get_db_object(self, session: Session) -> Reply:
        '''
        Override DownloadJob.
        '''
        return session.query(Reply).filter_by(uuid=self.uuid).one()

    def call_download_api(self, api: API, db_object: Reply) -> Tuple[str, str]:
        '''
        Override DownloadJob.
        '''
        sdk_object = SdkReply(uuid=db_object.uuid, filename=db_object.filename)
        sdk_object.source_uuid = db_object.source.uuid
        return api.download_reply(sdk_object)

    def call_decrypt(self, filepath: str, session: Session = None) -> None:
        '''
        Override DownloadJob.

        Decrypt the file located at the given filepath and store its plaintext content in the local
        database.

        The file containing the plaintext should be deleted once the content is stored in the db.
        '''
        with NamedTemporaryFile('w+') as plaintext_file:
            self.gpg.decrypt_submission_or_reply(filepath, plaintext_file.name, is_doc=False)
            set_message_or_reply_content(
                model_type=Reply,
                uuid=self.uuid,
                session=session,
                content=plaintext_file.read())


class MessageDownloadJob(DownloadJob):
    '''
    Download and decrypt a message from a source.
    '''

    def __init__(self, uuid: str, data_dir: str, gpg: GpgHelper) -> None:
        super().__init__(data_dir)
        self.uuid = uuid
        self.gpg = gpg

    def get_db_object(self, session: Session) -> Message:
        '''
        Override DownloadJob.
        '''
        return session.query(Message).filter_by(uuid=self.uuid).one()

    def call_download_api(self, api: API, db_object: Message) -> Tuple[str, str]:
        '''
        Override DownloadJob.
        '''
        sdk_object = SdkSubmission(uuid=db_object.uuid)
        sdk_object.source_uuid = db_object.source.uuid
        sdk_object.filename = db_object.filename
        return api.download_submission(sdk_object)

    def call_decrypt(self, filepath: str, session: Session = None) -> None:
        '''
        Override DownloadJob.

        Decrypt the file located at the given filepath and store its plaintext content in the local
        database.

        The file containing the plaintext should be deleted once the content is stored in the db.
        '''
        with NamedTemporaryFile('w+') as plaintext_file:
            self.gpg.decrypt_submission_or_reply(filepath, plaintext_file.name, is_doc=False)
            set_message_or_reply_content(
                model_type=Message,
                uuid=self.uuid,
                session=session,
                content=plaintext_file.read())


class FileDownloadJob(DownloadJob):
    '''
    Download and decrypt a file from a source.
    '''

    def __init__(self, uuid: str, data_dir: str, gpg: GpgHelper) -> None:
        super().__init__(data_dir)
        self.uuid = uuid
        self.gpg = gpg

    def get_db_object(self, session: Session) -> File:
        '''
        Override DownloadJob.
        '''
        return session.query(File).filter_by(uuid=self.uuid).one()

    def call_download_api(self, api: API, db_object: File) -> Tuple[str, str]:
        '''
        Override DownloadJob.
        '''
        sdk_object = SdkSubmission(uuid=db_object.uuid)
        sdk_object.source_uuid = db_object.source.uuid
        sdk_object.filename = db_object.filename
        return api.download_submission(sdk_object)

    def call_decrypt(self, filepath: str, session: Session = None) -> None:
        '''
        Override DownloadJob.

        Decrypt the file located at the given filepath and store its plaintext content in a file on
        the filesystem.

        The file storing the plaintext should have the same name as the downloaded file but without
        the file extensions, e.g. 1-impractical_thing-doc.gz.gpg -> 1-impractical_thing-doc
        '''
        fn_no_ext, _ = os.path.splitext(os.path.splitext(os.path.basename(filepath))[0])
        plaintext_filepath = os.path.join(self.data_dir, fn_no_ext)
        self.gpg.decrypt_submission_or_reply(filepath, plaintext_filepath, is_doc=True)
