import itertools
import logging

from PyQt5.QtCore import QObject, QThread, pyqtSlot
from queue import PriorityQueue
from sdclientapi import API, RequestTimeoutError
from sqlalchemy.orm import scoped_session
from typing import Optional, Tuple  # noqa: F401

from securedrop_client.api_jobs.base import ApiJob, ApiInaccessibleError, DEFAULT_NUM_ATTEMPTS
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
        self._process(False)

    def _process(self, exit_loop: bool) -> None:
        while True:
            session = self.session_maker()
            priority, job = self.queue.get(block=True)

            try:
                job._do_call_api(self.api_client, session)
            except RequestTimeoutError:
                logger.debug('Job {} timed out'.format(job))

                # Reset number of remaining attempts for this job to the default and
                # resubmit job without modifying counter to ensure jobs with equal
                # priorities are processed in the order that they were submitted
                # _by the user_ to the queue.
                job.remaining_attempts = DEFAULT_NUM_ATTEMPTS
                self.queue.put_nowait((priority, job))
            except ApiInaccessibleError:
                # This is a guard against #397, we should re-enqueue the job and pause queue
                # processing when this happens in the future and flag the situation to the user
                # (see ticket #379).
                logger.error('Client is not authenticated, skipping job...')
            except Exception as e:
                logger.error('Job {} raised  exception: {}: {}'.format(job, type(e).__name__, e))
            finally:
                session.close()

            if exit_loop:
                return


class ApiJobQueue(QObject):
    # These are the priorities for processing jobs.
    # Lower numbers corresponds to a higher priority.
    JOB_PRIORITIES = {
        # LogoutJob: 11,  # Not yet implemented
        # MetadataSyncJob: 12,  # Not yet implemented
        FileDownloadJob: 13,  # File downloads processed in separate queue
        MessageDownloadJob: 13,
        ReplyDownloadJob: 13,
        # DeletionJob: 14,  # Not yet implemented
        SendReplyJob: 15,
        UpdateStarJob: 16,
        # FlagJob: 16,  # Not yet implemented
    }

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

    def enqueue(self, job: ApiJob) -> None:
        # Additional defense in depth to prevent jobs being added to the queue when not
        # logged in.
        if not self.main_queue.api_client or not self.download_file_queue.api_client:
            logger.info('Not adding job, we are not logged in')
            return

        # First check the queues are started in case they died for some reason.
        self.start_queues()

        priority = self.JOB_PRIORITIES[type(job)]

        if isinstance(job, FileDownloadJob):
            logger.debug('Adding job to download queue')
            self.download_file_queue.add_job(priority, job)
        else:
            logger.debug('Adding job to main queue')
            self.main_queue.add_job(priority, job)
