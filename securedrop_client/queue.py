import itertools
import logging

from PyQt5.QtCore import QObject, QThread, pyqtSlot, pyqtSignal
from queue import PriorityQueue
from sdclientapi import API, RequestTimeoutError
from sqlalchemy.orm import scoped_session
from typing import Optional, Tuple  # noqa: F401

from securedrop_client.api_jobs.base import ApiJob, ApiInaccessibleError, DEFAULT_NUM_ATTEMPTS, \
    PauseQueueJob
from securedrop_client.api_jobs.downloads import (FileDownloadJob, MessageDownloadJob,
                                                  ReplyDownloadJob)
from securedrop_client.api_jobs.uploads import SendReplyJob
from securedrop_client.api_jobs.updatestar import UpdateStarJob


logger = logging.getLogger(__name__)


class RunnableQueue(QObject):
    '''
    RunnableQueue maintains a priority queue and processes jobs in that queue. It continuously
    processes the next job in the queue, which is ordered by highest priority. Priority is based on
    job type. If multiple jobs of the same type are added to the queue then they are retrieved
    in FIFO order.

    If a RequestTimeoutError or ApiInaccessibleError is encountered while processing a job, the
    job will be added back to the queue and a pause signal will be emitted. However the processing
    loop will not stop until a PauseQueueJob is retrieved. Once this happens, all processing stops.
    New jobs can still be added, but the processing function will need to be called again in order
    to resume. The processing loop is resumed when the resume signal is emitted.

    Any other exception encountered while processing a job is unexpected, so the queue will drop the
    job and continue on to processing the next job. The job itself is responsible for emiting the
    success and failure signals, so when an unexpected error occurs, it should emit the failure
    signal so that the Controller can respond accordingly.
    '''

    '''
    Signal that is emitted BEFORE a queue is paused
    '''
    pause = pyqtSignal()

    '''
    Signal that is emitted to resume processing jobs
    '''
    resume = pyqtSignal()

    def __init__(self, api_client: API, session_maker: scoped_session) -> None:
        super().__init__()
        self.api_client = api_client
        self.session_maker = session_maker
        self.queue = PriorityQueue()  # type: PriorityQueue[Tuple[int, ApiJob]]
        # `order_number` ensures jobs with equal priority are retrived in FIFO order. This is needed
        # because PriorityQueue is implemented using heapq which does not have sort stability. For
        # more info, see : https://bugs.python.org/issue17794
        self.order_number = itertools.count()

        # Rsume signals to resume processing
        self.resume.connect(self.process)

    def add_job(self, priority: int, job: ApiJob) -> None:
        '''
        Add the job with its priority to the queue after assigning it the next order_number.
        '''
        current_order_number = next(self.order_number)
        job.order_number = current_order_number
        self.queue.put_nowait((priority, job))

    @pyqtSlot()
    def process(self) -> None:
        '''
        Process the next job in the queue.

        If the job is a PauseQueueJob, return from the processing loop so that no more jobs are
        processed until the queue resumes.

        If the job raises RequestTimeoutError or ApiInaccessibleError, then:
        (1) Emit the pause signal so that a PauseQueueJob is enqueued
        (2) Put the job back into the queue in the order in which it was submitted by the user

        Note: Generic exceptions are handled in _do_call_api.
        '''
        while True:
            priority, job = self.queue.get(block=True)

            if isinstance(job, PauseQueueJob):
                logger.debug('Paused queue')
                return

            try:
                session = self.session_maker()
                job._do_call_api(self.api_client, session)
            except (RequestTimeoutError, ApiInaccessibleError) as e:
                logger.debug('Job {} raised an exception: {}: {}'.format(self, type(e).__name__, e))
                logger.debug('Pausing queue')
                self.pause.emit()
                job.remaining_attempts = DEFAULT_NUM_ATTEMPTS
                self.queue.put_nowait((priority, job))
            except Exception as e:
                logger.error('Job {} raised an exception: {}: {}'.format(self, type(e).__name__, e))
                logger.error('Skipping job')
            finally:
                session.close()


class ApiJobQueue(QObject):
    # These are the priorities for processing jobs.
    # Lower numbers corresponds to a higher priority.
    JOB_PRIORITIES = {
        # TokenInvalidationJob: 10,  # Not yet implemented
        PauseQueueJob: 11,
        # MetadataSyncJob: 12,  # Not yet implemented
        FileDownloadJob: 13,  # File downloads processed in separate queue
        MessageDownloadJob: 13,
        ReplyDownloadJob: 13,
        # DeletionJob: 14,  # Not yet implemented
        SendReplyJob: 15,
        UpdateStarJob: 16,
        # FlagJob: 16,  # Not yet implemented
    }

    '''
    Signal that is emitted AFTER a queue is paused
    '''
    paused = pyqtSignal()

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

        self.main_queue.pause.connect(self.pause_queues)
        self.download_file_queue.pause.connect(self.pause_queues)

    def logout(self) -> None:
        self.main_queue.api_client = None
        self.download_file_queue.api_client = None

    def login(self, api_client: API) -> None:
        logger.debug('Passing API token to queues')

        # Setting realistic (shorter) timeout for general requests so that user feedback
        # is faster
        api_client.default_request_timeout = 5

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

    def pause_queues(self) -> None:
        self.enqueue(PauseQueueJob())

    def resume_queues(self) -> None:
        logger.info("Resuming queues")
        self.start_queues()
        self.main_queue.resume.emit()
        self.download_file_queue.resume.emit()

    def enqueue(self, job: ApiJob) -> None:
        priority = self.JOB_PRIORITIES[type(job)]

        if isinstance(job, PauseQueueJob):
            self.main_queue.add_job(priority, job)
            self.download_file_queue.add_job(priority, job)
            self.paused.emit()
            return

        # Prevent api jobs being added to the queue when not logged in.
        if not self.main_queue.api_client or not self.download_file_queue.api_client:
            logger.info('Not adding job, we are not logged in')
            return

        # First check the queues are started in case they died for some reason.
        self.start_queues()

        if isinstance(job, FileDownloadJob):
            logger.debug('Adding job to download queue')
            self.download_file_queue.add_job(priority, job)
        else:
            logger.debug('Adding job to main queue')
            self.main_queue.add_job(priority, job)
