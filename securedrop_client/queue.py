import logging

from PyQt5.QtCore import QObject, QThread, pyqtSlot
from queue import PriorityQueue
from sdclientapi import API, RequestTimeoutError
from sqlalchemy.orm import scoped_session
from typing import Optional  # noqa: F401

from securedrop_client.api_jobs.base import ApiJob, ApiInaccessibleError, DEFAULT_NUM_ATTEMPTS
from securedrop_client.api_jobs.downloads import FileDownloadJob, MessageDownloadJob, ReplyDownloadJob
from securedrop_client.api_jobs.uploads import SendReplyJob
from securedrop_client.api_jobs.updatestar import UpdateStarJob


logger = logging.getLogger(__name__)

# These are the priorities for processing jobs.
# Lower numbers corresponds to a higher priority.
JOB_PRIORITIES = {
    # LogoutJob: 1,  # Not yet implemented
    # MetadataSyncJob: 2,  # Not yet implemented
    FileDownloadJob: 3,  # File downloads processed in separate queue
    MessageDownloadJob: 3,
    ReplyDownloadJob: 3,
    # DeletionJob: 4,  # Not yet implemented
    SendReplyJob: 5,
    UpdateStarJob: 6,
    # FlagJob: 6,  # Not yet implemented
}


class RunnableQueue(QObject):

    def __init__(self, api_client: API, session_maker: scoped_session) -> None:
        super().__init__()
        self.api_client = api_client
        self.session_maker = session_maker
        self.queue = PriorityQueue()  # type: PriorityQueue[ApiJob]
        self.last_job = None  # type: Optional[ApiJob]

    @pyqtSlot()
    def process(self) -> None:  # pragma: nocover
        self._process(False)

    def _process(self, exit_loop: bool) -> None:
        while True:
            session = self.session_maker()
            # retry the "cached" job if it exists, otherwise get the next job
            if self.last_job is not None:
                job = self.last_job
                self.last_job = None
            else:
                priority, job = self.queue.get(block=True)

            try:
                job._do_call_api(self.api_client, session)
            except RequestTimeoutError:
                # Reset number of remaining attempts for this job to the default
                job.remaining_attempts = DEFAULT_NUM_ATTEMPTS
                self.last_job = job  # "cache" the last job since we can't re-queue it
            except ApiInaccessibleError:
                # This is a guard against #397, we should pause the queue execution when this
                # happens in the future and flag the situation to the user (see ticket #379).
                logger.error('Client is not authenticated, skipping job...')
            finally:
                session.close()

            if exit_loop:
                return


class ApiJobQueue(QObject):

    def __init__(self, api_client: API, session_maker: scoped_session) -> None:
        super().__init__(None)
        self.api_client = api_client

        self.main_thread = QThread()
        self.download_file_thread = QThread()

        self.main_queue = RunnableQueue(self.api_client, session_maker)
        self.download_file_queue = RunnableQueue(self.api_client, session_maker)

        self.main_queue.moveToThread(self.main_thread)
        self.download_file_queue.moveToThread(self.download_file_thread)

        self.main_thread.started.connect(self.main_queue.process)
        self.download_file_thread.started.connect(self.download_file_queue.process)

    def logout(self) -> None:
        self.main_queue.api_client = None
        self.download_file_queue.api_client = None

    def login(self, api_client: API) -> None:
        logger.debug('Passing API token to queues')
        self.main_queue.api_client = api_client
        self.download_file_queue.api_client = api_client
        self.start_queues()

    def start_queues(self) -> None:
        if not self.main_thread.isRunning():
            logger.debug('Starting main thread')
            self.main_thread.start()

        if not self.download_file_thread.isRunning():
            logger.debug('Starting download thread')
            self.download_file_thread.start()

    def enqueue(self, job: ApiJob) -> None:
        # Additional defense in depth to prevent jobs being added to the queue when not
        # logged in.
        if not self.main_queue.api_client or not self.download_file_queue.api_client:
            logger.info('Not adding job, we are not logged in')
            return

        # First check the queues are started in case they died for some reason.
        self.start_queues()

        # Get job priority
        priority = JOB_PRIORITIES[type(job)]

        if isinstance(job, FileDownloadJob):
            logger.debug('Adding job to download queue')
            self.download_file_queue.queue.put_nowait((priority, job))
        else:
            logger.debug('Adding job to main queue')
            self.main_queue.queue.put_nowait((priority, job))
