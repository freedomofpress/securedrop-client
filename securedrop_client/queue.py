import binascii
import hashlib
import logging
import os
import sdclientapi
import shutil

from PyQt5.QtCore import QObject, QThread, pyqtSlot, pyqtSignal
from PyQt5.QtWidgets import QApplication
from queue import Queue
from sdclientapi import API, RequestTimeoutError, AuthError
from typing import Any, Union, Optional, Type, Tuple

from securedrop_client import storage
from securedrop_client.crypto import GpgHelper, CryptoError
from securedrop_client.db import Session, File, Message


logger = logging.getLogger(__name__)


class ApiInaccessibleError(Exception):

    def __init__(self, message: Optional[str] = None) -> None:
        if not message:
            message = ('API is inaccessible either because there is no client or because the '
                       'client is not properly authenticated.')
        super().__init__(message)


class ApiJob(QObject):

    '''
    Signal that is emitted after an job finishes successfully.
    '''
    success_signal = pyqtSignal('PyQt_PyObject')

    '''
    Signal that is emitted if there is a failure during the job.
    '''
    failure_signal = pyqtSignal(Exception)

    def __init__(self) -> None:
        super().__init__(None)  # `None` because the QOjbect has no parent

    def _do_call_api(self, api_client: API, session: Session) -> None:
        if not api_client:
            raise ApiInaccessibleError()

        try:
            result = self.call_api(api_client, session)
        except AuthError as e:
            raise ApiInaccessibleError() from e
        except RequestTimeoutError:
            logger.debug('Job {} timed out'.format(self))
            raise
        except Exception as e:
            logger.error('Job {} raised an exception: {}: {}'
                         .format(self, type(e).__name__, e))
            self.failure_signal.emit(e)
        else:
            self.success_signal.emit(result)

    def call_api(self, api_client: API, session: Session) -> Any:
        '''
        Method for making the actual API call and handling the result.

        This MUST resturn a value if the API call and other tasks were successful and MUST raise
        an exception if and only iff the tasks failed. Presence of a raise exception indicates a
        failure.
        '''
        raise NotImplementedError


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


class RunnableQueue(QObject):

    def __init__(self, api_client: API) -> None:
        super().__init__()
        self.api_client = api_client
        self.queue = Queue()  # type: Queue[ApiJob]
        self.last_job = None  # type: Optional[ApiJob]

    @pyqtSlot()
    def process(self) -> None:  # pragma: nocover
        self._process(False)

    def _process(self, exit_loop: bool) -> None:
        session = Session()
        while True:
            # retry the "cached" job if it exists, otherwise get the next job
            if self.last_job is not None:
                job = self.last_job
                self.last_job = None
            else:
                job = self.queue.get(block=True)

            try:
                job._do_call_api(self.api_client, session)
            except RequestTimeoutError:
                self.last_job = job  # "cache" the last job since we can't re-queue it
                return

            # process events to allow this thread to handle incoming signals
            QApplication.processEvents()

            if exit_loop:
                return


class ApiJobQueue(QObject):

    def __init__(self, api_client: API) -> None:
        super().__init__(None)
        self.api_client = api_client

        self.main_thread = QThread()
        self.download_thread = QThread()

        self.main_queue = RunnableQueue(self.api_client)
        self.download_queue = RunnableQueue(self.api_client)

        self.main_queue.moveToThread(self.main_thread)
        self.download_queue.moveToThread(self.download_thread)

        self.main_thread.started.connect(self.main_queue.process)
        self.download_thread.started.connect(self.download_queue.process)

    def start_queues(self, api_client: API) -> None:
        self.main_queue.api_client = api_client
        self.download_queue.api_client = api_client

        self.main_thread.start()
        self.download_thread.start()

    def enqueue(self, job: ApiJob) -> None:
        if isinstance(job, DownloadSubmissionJob):
            self.download_queue.queue.put_nowait(job)
        else:
            self.main_queue.queue.put_nowait(job)
