import logging

from PyQt5.QtCore import pyqtSignal, QObject, QThread, QTimer, Qt
from sqlalchemy.orm import scoped_session
from sdclientapi import API, RequestTimeoutError

from securedrop_client.api_jobs.sync import MetadataSyncJob
from securedrop_client.crypto import GpgHelper


logger = logging.getLogger(__name__)


class ApiSync(QObject):
    '''
    ApiSync continuously executes a MetadataSyncJob, waiting 15 seconds between jobs.
    '''
    sync_started = pyqtSignal()
    sync_success = pyqtSignal()
    sync_failure = pyqtSignal(Exception)

    TIME_BETWEEN_SYNCS_MS = 1000 * 15  # fifteen seconds between syncs

    def __init__(
        self, api_client: API, session_maker: scoped_session, gpg: GpgHelper, data_dir: str
    ):
        super().__init__()

        self.api_client = api_client
        self.session_maker = session_maker
        self.gpg = gpg
        self.data_dir = data_dir

        self.sync_thread = QThread()
        self.sync_thread.started.connect(self._sync)

    def start(self, api_client: API) -> None:
        '''
        Stop metadata syncs.
        '''
        self.api_client = api_client

        if not self.sync_thread.isRunning():
            logger.debug('Starting sync thread')
            self.sync_thread.start()

    def stop(self):
        '''
        Stop metadata syncs.
        '''
        self.api_client = None

        if self.sync_thread.isRunning():
            logger.debug('Stopping sync thread')
            self.sync_thread.quit()

    def sync(self):
        '''
        Create and run a new MetadataSyncJob.
        '''
        job = MetadataSyncJob(self.data_dir, self.gpg)
        job.success_signal.connect(self.on_sync_success, type=Qt.QueuedConnection)
        job.failure_signal.connect(self.on_sync_failure, type=Qt.QueuedConnection)

        session = self.session_maker()
        job._do_call_api(self.api_client, session)
        self.sync_started.emit()

    def on_sync_success(self) -> None:
        self.sync_success.emit()
        QTimer.singleShot(self.TIME_BETWEEN_SYNCS_MS, self.sync)

    def on_sync_failure(self, result: Exception) -> None:
        self.sync_failure.emit(result)
        if isinstance(result, RequestTimeoutError):
            QTimer.singleShot(self.TIME_BETWEEN_SYNCS_MS, self.sync)
