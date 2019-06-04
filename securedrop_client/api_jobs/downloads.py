import binascii
import hashlib
import logging
import os
import sdclientapi
import shutil

from sdclientapi import API
from sqlalchemy.orm.session import Session
from typing import Any, Union, Type, Tuple

from securedrop_client import storage
from securedrop_client.api_jobs.base import ApiJob
from securedrop_client.crypto import GpgHelper, CryptoError
from securedrop_client.db import File, Message


logger = logging.getLogger(__name__)


class DownloadSubmissionJob(ApiJob):

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
        storage.mark_file_as_downloaded(file_uuid, session)

        try:
            self.gpg.decrypt_submission_or_reply(filepath_in_datadir, server_filename, is_doc=True)
        except CryptoError as e:
            logger.debug('Failed to decrypt file {}: {}'.format(server_filename, e))
            storage.set_object_decryption_status_with_content(db_object, session, False)
            raise e

        storage.set_object_decryption_status_with_content(db_object, session, True)
