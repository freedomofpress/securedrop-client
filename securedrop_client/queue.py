import itertools
import logging

from PyQt5.QtCore import QObject, QThread, pyqtSlot, pyqtSignal
from queue import PriorityQueue, Full
from sdclientapi import API, RequestTimeoutError
from sqlalchemy.orm import scoped_session
from typing import Optional, Tuple  # noqa: F401

from securedrop_client.api_jobs.base import ApiJob, ApiInaccessibleError, DEFAULT_NUM_ATTEMPTS, \
    PauseQueueJob
from securedrop_client.api_jobs.downloads import (FileDownloadJob, MessageDownloadJob,
                                                  ReplyDownloadJob)
from securedrop_client.api_jobs.sources import DeleteSourceJob
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

    # These are the priorities for processing jobs. Lower numbers corresponds to a higher priority.
    JOB_PRIORITIES = {
        # TokenInvalidationJob: 10,  # Not yet implemented
        PauseQueueJob: 11,
        FileDownloadJob: 13,  # File downloads processed in separate queue
        DeleteSourceJob: 14,
        SendReplyJob: 15,
        UpdateStarJob: 16,
        MessageDownloadJob: 17,
        ReplyDownloadJob: 17,
    }

    '''
    Signal that is emitted when processing stops
    '''
    paused = pyqtSignal()

    '''
    Signal that is emitted to resume processing jobs
    '''
    resume = pyqtSignal()

    def __init__(self, api_client: API, session_maker: scoped_session, size: int = 0) -> None:
        """
        A size of zero means there's no upper bound to the queue size.
        """
        super().__init__()
        self.api_client = api_client
        self.session_maker = session_maker
        self.queue = PriorityQueue(maxsize=size)  # type: PriorityQueue[Tuple[int, ApiJob]]
        # `order_number` ensures jobs with equal priority are retrived in FIFO order. This is needed
        # because PriorityQueue is implemented using heapq which does not have sort stability. For
        # more info, see : https://bugs.python.org/issue17794
        self.order_number = itertools.count()

        # Rsume signals to resume processing
        self.resume.connect(self.process)

    def add_job(self, job: ApiJob) -> None:
        '''
        Add the job with its priority to the queue after assigning it the next order_number.
        '''
        current_order_number = next(self.order_number)
        job.order_number = current_order_number
        priority = self.JOB_PRIORITIES[type(job)]
        try:
            self.queue.put_nowait((priority, job))
        except Full:
            pass  # Pass silently if the queue is full

    def re_add_job(self, job: ApiJob) -> None:
        '''
        Reset the job's remaining attempts and put it back into the queue in the order in which it
        was submitted by the user (do not assign it the next order_number).
        '''
        job.remaining_attempts = DEFAULT_NUM_ATTEMPTS
        priority = self.JOB_PRIORITIES[type(job)]
        try:
            self.queue.put_nowait((priority, job))
        except Full:
            pass  # Pass silently if the queue is full

    @pyqtSlot()
    def process(self) -> None:
        '''
        Process the next job in the queue.

        If the job is a PauseQueueJob, emit the paused signal and return from the processing loop so
        that no more jobs are processed until the queue resumes.

        If the job raises RequestTimeoutError, then:
        (1) Add a PauseQueuejob to the queue
        (2) Add the job back to the queue so that it can be reprocessed once the queue is resumed.

        If the job raises ApiInaccessibleError, then:
        (1) Set the token to None so that the queue manager will stop enqueuing jobs since we are
        no longer able to make api requests.
        (2) Return from the processing loop since a valid token will be needed in order to process
        jobs.

        Note: Generic exceptions are handled in _do_call_api.
        '''
        logger.debug('Beginning queue processing loop')

        while True:
            priority, job = self.queue.get(block=True)

            if isinstance(job, PauseQueueJob):
                logger.debug('Paused queue')
                self.paused.emit()
                return

            try:
                session = self.session_maker()
                job._do_call_api(self.api_client, session)
            except ApiInaccessibleError as e:
                logger.debug('Job {} raised an exception: {}: {}'.format(self, type(e).__name__, e))
                self.api_client = None
                return
            except RequestTimeoutError as e:
                logger.debug('Job {} raised an exception: {}: {}'.format(self, type(e).__name__, e))
                self.add_job(PauseQueueJob())
                self.re_add_job(job)
            except Exception as e:
                logger.error('Job {} raised an exception: {}: {}'.format(self, type(e).__name__, e))
                logger.error('Skipping job')
            finally:
                session.close()


class ApiJobQueue(QObject):
    '''
    Signal that is emitted after a queue is paused
    '''
    paused = pyqtSignal()

    def __init__(self, api_client: API, session_maker: scoped_session) -> None:
        super().__init__(None)

        self.main_thread = QThread()
        self.download_file_thread = QThread()

        self.main_queue = RunnableQueue(api_client, session_maker)
        self.download_file_queue = RunnableQueue(api_client, session_maker)

        self.main_queue.moveToThread(self.main_thread)
        self.download_file_queue.moveToThread(self.download_file_thread)

        self.main_thread.started.connect(self.main_queue.process)
        self.download_file_thread.started.connect(self.download_file_queue.process)

        self.main_queue.paused.connect(self.on_queue_paused)
        self.download_file_queue.paused.connect(self.on_queue_paused)

    def logout(self) -> None:
        if self.main_thread.isRunning():
            logger.debug('Stopping main queue thread')
            self.main_thread.quit()

        if self.download_file_thread.isRunning():
            logger.debug('Stopping download queue thread')
            self.download_file_thread.quit()

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

    def on_queue_paused(self) -> None:
        self.paused.emit()

    def resume_queues(self) -> None:
        if self.main_thread.isRunning():
            self.main_queue.resume.emit()
        if self.download_file_thread.isRunning():
            self.download_file_queue.resume.emit()

    def enqueue(self, job: ApiJob) -> None:
        # Prevent api jobs being added to the queue when not logged in.
        if (not self.main_queue.api_client or not self.download_file_queue.api_client):
            logger.info('Not adding job, we are not logged in')
            return

        # First check the queues are started in case they died for some reason.
        self.start_queues()

        if isinstance(job, FileDownloadJob):
            logger.debug('Adding job to download queue')
            self.download_file_queue.add_job(job)
        else:
            logger.debug('Adding job to main queue')
            self.main_queue.add_job(job)
