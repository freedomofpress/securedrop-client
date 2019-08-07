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

    def __init__(self, api_client: API, session_maker: scoped_session) -> None:
        super().__init__()
        self.api_client = api_client
        self.session_maker = session_maker
        self.queue = PriorityQueue()  # type: PriorityQueue[Tuple[int, ApiJob]]

        # One of the challenges of using Python's PriorityQueue is that
        # for objects (jobs) with equal priorities, they are not retrieved
        # in FIFO order due to the fact PriorityQueue is implemented using
        # heapq which does not have sort stability. In order to ensure sort
        # stability, we need to add a counter to ensure that objects with equal
        # priorities are retrived in FIFO order.
        # See also: https://bugs.python.org/issue17794
        self.order_number = itertools.count()

    def add_job(self, priority: int, job: ApiJob) -> None:
        """
        Increment the queue's internal counter/order_number, assign an
        order_number to the job to track its position in the queue,
        and submit the job with its priority to the queue.
        """

        current_order_number = next(self.order_number)
        job.order_number = current_order_number
        self.queue.put_nowait((priority, job))

    @pyqtSlot()
    def process(self) -> None:  # pragma: nocover
        while True:
            session = self.session_maker()
            priority, job = self.queue.get(block=True)

            if isinstance(job, PauseQueueJob):
                logger.info('Paused queue')
                return

            try:
                job._do_call_api(self.api_client, session)
            except RequestTimeoutError:
                # Reset number of remaining attempts for this job to the default
                job.remaining_attempts = DEFAULT_NUM_ATTEMPTS

                # Resubmit job without modifying counter to ensure jobs with equal
                # priorities are processed in the order that they were submitted
                # _by the user_ to the queue.
                self.queue.put_nowait((priority, job))
                self.pause()
            except ApiInaccessibleError:
                # This is a guard against #397, we should pause the queue execution when this
                # happens in the future and flag the situation to the user (see ticket #379).
                logger.error('Client is not authenticated, skipping job...')
            finally:
                session.close()

    def pause(self):
        self.queue.enqueue(PauseQueueJob())

    def resume(self):
        self.process()


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
    Signal that is emitted if a queue is paused
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

    def resume_queues(self) -> None:
        logger.info("Resuming queues")
        # Reconnect the queues to the processing loop and restart the threads
        self.main_thread.started.connect(self.main_queue.process)
        self.download_file_thread.started.connect(self.download_file_queue.process)
        self.main_thread.start()
        self.download_file_thread.start()

    def enqueue(self, job: ApiJob) -> None:
        # Additional defense in depth to prevent jobs being added to the queue when not
        # logged in.
        if not self.main_queue.api_client or not self.download_file_queue.api_client:
            logger.info('Not adding job, we are not logged in')
            return

        # First check the queues are started in case they died for some reason.
        self.start_queues()

        priority = self.JOB_PRIORITIES[type(job)]

        if isinstance(job, PauseQueueJob):
            logger.debug('Adding pause job to both queues')
            self.main_queue.add_job(priority, job)
            self.download_file_queue.add_job(priority, job)
            # Disconnect queues from processing loop in case threads restart while paused
            self.main_thread.started.disconnect()
            self.download_file_thread.started.disconnect()
            # Tell the gui that the queues are now paused
            self.paused.emit()
        elif isinstance(job, FileDownloadJob):
            logger.debug('Adding job to download queue')
            self.download_file_queue.add_job(priority, job)
        else:
            logger.debug('Adding job to main queue')
            self.main_queue.add_job(priority, job)
