import binascii
import hashlib
import logging
import math
import os
import shutil

from tempfile import NamedTemporaryFile
from typing import Any, Union, Tuple, Type

from sdclientapi import API, BaseError
from sdclientapi import Reply as SdkReply
from sdclientapi import Submission as SdkSubmission
from sqlalchemy.orm.session import Session

from securedrop_client.api_jobs.base import ApiJob
from securedrop_client.crypto import GpgHelper, CryptoError
from securedrop_client.db import DownloadError, DownloadErrorCodes, File, Message, Reply
from securedrop_client.storage import mark_as_decrypted, mark_as_downloaded, \
    set_message_or_reply_content


logger = logging.getLogger(__name__)


class DownloadException(Exception):
    def __init__(self, message: str,
                 object_type: Union[Type[Reply], Type[Message], Type[File]],
                 uuid: str):
        super().__init__(message)
        self.object_type = object_type
        self.uuid = uuid


class DownloadChecksumMismatchException(DownloadException):
    """
    Raised when a download's hash does not match the SecureDrop server's.
    """


class DownloadDecryptionException(DownloadException):
    """
    Raised when an error occurs during decryption of a download.
    """


class DownloadJob(ApiJob):
    '''
    Download and decrypt a file that contains either a message, reply, or file submission.
    '''

    CHUNK_SIZE = 4096

    def __init__(self, data_dir: str) -> None:
        super().__init__()
        self.data_dir = data_dir

    def _get_realistic_timeout(self, size_in_bytes: int) -> int:
        '''
        Return a realistic timeout in seconds based on the size of the download.

        This simply scales the timeouts per file so that it increases as the file size increases.

        Note that:

        * The size of the file provided by server is in bytes (the server computes it using
          os.stat.ST_SIZE).

        * The following times are reasonable estimations for how long it should take to fetch a
          file over Tor according to Tor metrics given a recent three month period in 2019:

          50 KiB  (51200 bytes)   =  4   seconds  (  12800 bytes/second)
          1  MiB  (1049000 bytes) =  7.5 seconds  (~139867 bytes/second)

          For more information, see:
          https://metrics.torproject.org/torperf.html?start=2019-05-02&end=2019-07-31&server=onion

        * As you might expect, this method returns timeouts that are larger than the expected
          download time, which is why the rates below are slower than what you see above with the
          Tor metrics, e.g. instead of setting TIMEOUT_BYTES_PER_SECOND to 139867 bytes/second, we
          set it to 100000 bytes/second.

        * Minimum timeout allowed is 25 seconds
        '''
        TIMEOUT_BYTES_PER_SECOND = 100000.0
        TIMEOUT_ADJUSTMENT_FACTOR = 1.5
        TIMEOUT_BASE = 25
        timeout = math.ceil((size_in_bytes / TIMEOUT_BYTES_PER_SECOND) * TIMEOUT_ADJUSTMENT_FACTOR)
        return timeout + TIMEOUT_BASE

    def call_download_api(self, api: API,
                          db_object: Union[File, Message, Reply]) -> Tuple[str, str]:
        '''
        Method for making the actual API call to downlod the file and handling the result.

        This MUST return the (etag, filepath) tuple response from the server and MUST raise an
        exception if and only if the download fails.
        '''
        raise NotImplementedError

    def call_decrypt(self, filepath: str, session: Session = None) -> str:
        '''
        Method for decrypting the file and storing the plaintext result.

        Returns the original filename.

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
        Override ApiJob.

        Download and decrypt the file associated with the database object.
        '''
        db_object = self.get_db_object(session)

        if db_object.is_decrypted:
            return db_object.uuid

        if db_object.is_downloaded:
            self._decrypt(db_object.location(self.data_dir), db_object, session)
            return db_object.uuid

        destination = self._download(api_client, db_object, session)
        self._decrypt(destination, db_object, session)
        return db_object.uuid

    def _download(self,
                  api: API,
                  db_object: Union[File, Message, Reply],
                  session: Session) -> str:
        '''
        Download the encrypted file. Check file integrity and move it to the data directory before
        marking it as downloaded.

        Note: On Qubes OS, files are downloaded to /home/user/QubesIncoming/sd-proxy
        '''
        try:
            etag, download_path = self.call_download_api(api, db_object)

            if not self._check_file_integrity(etag, download_path):
                download_error = session.query(DownloadError).filter_by(
                    name=DownloadErrorCodes.CHECKSUM_ERROR.name
                ).one()
                db_object.download_error = download_error
                session.commit()
                exception = DownloadChecksumMismatchException(
                    'Downloaded file had an invalid checksum.',
                    type(db_object),
                    db_object.uuid
                    )
                raise exception

            destination = db_object.location(self.data_dir)
            os.makedirs(os.path.dirname(destination), mode=0o700, exist_ok=True)
            shutil.move(download_path, destination)
            db_object.download_error = None
            mark_as_downloaded(type(db_object), db_object.uuid, session)
            logger.info("File downloaded to {}".format(destination))
            return destination
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
            original_filename = self.call_decrypt(filepath, session)
            db_object.download_error = None
            mark_as_decrypted(
                type(db_object), db_object.uuid, session, original_filename=original_filename
            )
            logger.info("File decrypted: {} (decrypted file in: {})".format(
                os.path.basename(filepath), os.path.dirname(filepath))
            )
        except CryptoError as e:
            mark_as_decrypted(type(db_object), db_object.uuid, session, is_decrypted=False)
            download_error = session.query(DownloadError).filter_by(
                name=DownloadErrorCodes.DECRYPTION_ERROR.name
            ).one()
            db_object.download_error = download_error
            session.commit()
            logger.debug("Failed to decrypt file: {}".format(os.path.basename(filepath)))
            raise DownloadDecryptionException(
                "Downloaded file could not be decrypted.",
                type(db_object),
                db_object.uuid
            ) from e

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

        # TODO: Once https://github.com/freedomofpress/securedrop-sdk/issues/108 is implemented, we
        # will want to pass the default request timeout to download_reply instead of setting it on
        # the api object directly.
        api.default_request_timeout = 20
        return api.download_reply(sdk_object)

    def call_decrypt(self, filepath: str, session: Session = None) -> str:
        '''
        Override DownloadJob.

        Decrypt the file located at the given filepath and store its plaintext content in the local
        database.

        The file containing the plaintext should be deleted once the content is stored in the db.

        The return value is an empty string; replies have no original filename.
        '''
        with NamedTemporaryFile('w+') as plaintext_file:
            self.gpg.decrypt_submission_or_reply(filepath, plaintext_file.name, is_doc=False)
            try:
                set_message_or_reply_content(
                    model_type=Reply,
                    uuid=self.uuid,
                    session=session,
                    content=plaintext_file.read())
            finally:
                # clean up directory where decryption happened
                try:
                    os.rmdir(os.path.dirname(filepath))
                except Exception as e:
                    logger.warning(
                        "Error deleting decryption directory of message %s: %s", self.uuid, e
                    )

        return ""


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
        return api.download_submission(sdk_object,
                                       timeout=self._get_realistic_timeout(db_object.size))

    def call_decrypt(self, filepath: str, session: Session = None) -> str:
        '''
        Override DownloadJob.

        Decrypt the file located at the given filepath and store its plaintext content in the local
        database.

        The file containing the plaintext should be deleted once the content is stored in the db.

        The return value is an empty string; messages have no original filename.
        '''
        with NamedTemporaryFile('w+') as plaintext_file:
            try:
                self.gpg.decrypt_submission_or_reply(filepath, plaintext_file.name, is_doc=False)
                set_message_or_reply_content(
                    model_type=Message,
                    uuid=self.uuid,
                    session=session,
                    content=plaintext_file.read())
            finally:
                # clean up directory where decryption happened
                try:
                    os.rmdir(os.path.dirname(filepath))
                except Exception as e:
                    logger.warning(
                        "Error deleting decryption directory of message %s: %s", self.uuid, e
                    )
        return ""


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
        return api.download_submission(sdk_object,
                                       timeout=self._get_realistic_timeout(db_object.size))

    def call_decrypt(self, filepath: str, session: Session = None) -> str:
        '''
        Override DownloadJob.

        Decrypt the file located at the given filepath and store its plaintext content in a file on
        the filesystem.

        The file storing the plaintext should have the same name as the downloaded file but without
        the file extensions, e.g. 1-impractical_thing-doc.gz.gpg -> 1-impractical_thing-doc
        '''
        fn_no_ext, _ = os.path.splitext(os.path.splitext(os.path.basename(filepath))[0])
        plaintext_filepath = os.path.join(os.path.dirname(filepath), fn_no_ext)
        original_filename = self.gpg.decrypt_submission_or_reply(
            filepath, plaintext_filepath, is_doc=True
        )
        logger.info("Decrypted file '{}' to folder '{}'".format(
            os.path.basename(filepath), os.path.dirname(filepath)))
        return original_filename
