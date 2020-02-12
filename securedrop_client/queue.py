import itertools
import logging

from PyQt5.QtCore import QObject, QThread, pyqtSlot, pyqtSignal
from queue import PriorityQueue
from sdclientapi import API, RequestTimeoutError, ServerConnectionError
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

    If a RequestTimeoutError or ServerConnectionError is encountered while processing a job, the
    job will be added back to the queue, the processing loop will stop, and the paused signal will
    be emitted. New jobs can still be added, but the processing function will need to be called
    again in order to resume. The processing loop is resumed when the resume signal is emitted.

    If an ApiInaccessibleError is encountered while processing a job, api_client will be set to
    None and the processing loop will stop. If the queue is resumed before the queue manager
    stops the queue thread, api_client will still be None and the next job will raise an
    ApiInaccessibleError before it makes an api call, which will repeat this process.

    Any other exception encountered while processing a job is unexpected, so the queue will drop the
    job and continue on to processing the next job. The job itself is responsible for emiting the
    success and failure signals, so when an unexpected error occurs, it should emit the failure
    signal so that the Controller can respond accordingly.
    '''

    # These are the priorities for processing jobs. Lower numbers corresponds to a higher priority.
    JOB_PRIORITIES = {
        PauseQueueJob: 11,
        FileDownloadJob: 13,  # File downloads processed in separate queue
        DeleteSourceJob: 14,
        SendReplyJob: 15,
        UpdateStarJob: 16,
        MessageDownloadJob: 17,
        ReplyDownloadJob: 17,
    }

    # Signal that is emitted when processing stops
    paused = pyqtSignal()

    # Signal that is emitted to resume processing jobs
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

        self.resume.connect(self.process)

    def add_job(self, job: ApiJob) -> None:
        '''
        Add the job with its priority to the queue after assigning it the next order_number.
        '''
        current_order_number = next(self.order_number)
        job.order_number = current_order_number
        priority = self.JOB_PRIORITIES[type(job)]
        self.queue.put_nowait((priority, job))

    def re_add_job(self, job: ApiJob) -> None:
        '''
        Reset the job's remaining attempts and put it back into the queue in the order in which it
        was submitted by the user (do not assign it the next order_number).
        '''
        job.remaining_attempts = DEFAULT_NUM_ATTEMPTS
        priority = self.JOB_PRIORITIES[type(job)]
        self.queue.put_nowait((priority, job))

    @pyqtSlot()
    def process(self) -> None:
        '''
        Process the next job in the queue.

        If the job is a PauseQueueJob, emit the paused signal and return from the processing loop so
        that no more jobs are processed until the queue resumes.

        If the job raises RequestTimeoutError or ServerConnectionError, then:
        (1) Add a PauseQueuejob to the queue
        (2) Add the job back to the queue so that it can be reprocessed once the queue is resumed.

        If the job raises ApiInaccessibleError, then:
        (1) Set the token to None so that the queue manager will stop enqueuing jobs since we are
        no longer able to make api requests.
        (2) Return from the processing loop since a valid token will be needed in order to process
        jobs.

        Note: Generic exceptions are handled in _do_call_api.
        '''
        while True:
            priority, job = self.queue.get(block=True)

            if isinstance(job, PauseQueueJob):
                self.paused.emit()
                return

            try:
                session = self.session_maker()
                job._do_call_api(self.api_client, session)
            except ApiInaccessibleError as e:
                logger.debug('{}: {}'.format(type(e).__name__, e))
                self.api_client = None
                return
            except (RequestTimeoutError, ServerConnectionError) as e:
                logger.debug('{}: {}'.format(type(e).__name__, e))
                self.add_job(PauseQueueJob())
                self.re_add_job(job)
            except Exception as e:
                logger.error('{}: {}'.format(type(e).__name__, e))
                logger.debug('Skipping job')
            finally:
                session.close()


class ApiJobQueue(QObject):
    '''
    ApiJobQueue is the queue manager of two FIFO priority queues that process jobs of type ApiJob.


    The queue manager starts the queues when a new auth token is provided to ensure jobs are able to
    make their requests. It stops the queues whenever a MetadataSyncJob, which runs in a continuous
    loop outside of the queue manager, encounters an ApiInaccessibleError and forces a logout
    from the Controller.
    '''

    # Signal that is emitted after a queue is paused.
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

        self.main_queue.paused.connect(self.on_main_queue_paused)
        self.download_file_queue.paused.connect(self.on_file_download_queue_paused)

    def start(self, api_client: API) -> None:
        '''
        Start the queues whenever a new api token is provided.
        '''
        self.main_queue.api_client = api_client
        self.download_file_queue.api_client = api_client

        if not self.main_thread.isRunning():
            self.main_thread.start()
            logger.debug('Started main queue')

        if not self.download_file_thread.isRunning():
            self.download_file_thread.start()
            logger.debug('Started file download queue')

    def stop(self) -> None:
        '''
        Stop the queues.
        '''
        if self.main_thread.isRunning():
            self.main_thread.quit()
            logger.debug('Stopped main queue')

        if self.download_file_thread.isRunning():
            self.download_file_thread.quit()
            logger.debug('Stopped file download queue')

    @pyqtSlot()
    def on_main_queue_paused(self) -> None:
        '''
        Emit the paused signal if the main queue has been paused.
        '''
        logger.debug('Paused main queue')
        self.paused.emit()

    @pyqtSlot()
    def on_file_download_queue_paused(self) -> None:
        '''
        Emit the paused signal if the file download queue has been paused.
        '''
        logger.debug('Paused file download queue')
        self.paused.emit()

    def resume_queues(self) -> None:
        '''
        Emit the resume signal to the queues if they are running.
        '''
        if self.main_thread.isRunning():
            logger.debug("Resuming main queue")
            self.main_queue.resume.emit()
        if self.download_file_thread.isRunning():
            logger.debug("Resuming download queue")
            self.download_file_queue.resume.emit()

    def enqueue(self, job: ApiJob) -> None:
        '''
        Enqueue the supplied job if the queues are running.
        '''
        if not self.main_thread.isRunning() or not self.download_file_thread.isRunning():
            logger.debug('Not adding job before queues have been started.')
            return

        if isinstance(job, FileDownloadJob):
            self.download_file_queue.add_job(job)
            logger.debug('Added {} to download queue'.format(job.__class__.__name__))
        else:
            self.main_queue.add_job(job)
            logger.debug('Added {} to main queue'.format(job.__class__.__name__))
