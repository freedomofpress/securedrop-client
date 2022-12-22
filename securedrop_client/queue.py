import itertools
import logging
import threading
from queue import PriorityQueue
from typing import Any, Optional, Tuple

from PyQt5.QtCore import QObject, QThread, pyqtBoundSignal, pyqtSignal, pyqtSlot
from sdclientapi import API, RequestTimeoutError, ServerConnectionError
from sqlalchemy.orm import scoped_session

from securedrop_client.api_jobs.base import (
    DEFAULT_NUM_ATTEMPTS,
    ApiInaccessibleError,
    ApiJob,
    ClearQueueJob,
    PauseQueueJob,
    QueueJob,
)
from securedrop_client.api_jobs.downloads import (
    FileDownloadJob,
    MessageDownloadJob,
    ReplyDownloadJob,
)
from securedrop_client.api_jobs.seen import SeenJob
from securedrop_client.api_jobs.sources import DeleteConversationJob, DeleteSourceJob
from securedrop_client.api_jobs.updatestar import UpdateStarJob
from securedrop_client.api_jobs.uploads import SendReplyJob

logger = logging.getLogger(__name__)


class RunnablePriorityQueue(PriorityQueue):
    """
    Wrapper class around PriorityQueue that emits a signal when message or reply
    download jobs are enqueued or dequeued.
    """

    def __init__(
        self, *args: Any, queue_updated_signal: Optional[pyqtBoundSignal] = None, **kwargs: Any
    ):
        self.queue_updated_signal = queue_updated_signal
        super().__init__(*args, **kwargs)

    def get(self, *args: Any, **kwargs: Any) -> Tuple[int, QueueJob]:
        item = super().get(*args, **kwargs)
        if self.queue_updated_signal:
            self.queue_updated_signal.emit(self._get_num_message_or_reply_download_jobs())
        return item

    def put(self, *args: Any, **kwargs: Any) -> None:
        item = super().put(*args, **kwargs)
        if self.queue_updated_signal:
            self.queue_updated_signal.emit(self._get_num_message_or_reply_download_jobs())
        return item

    def _get_num_message_or_reply_download_jobs(self) -> int:
        message_and_reply_download_jobs = list(
            # PriorityQueue items are a tuple of (priority, job)
            filter(lambda job: type(job[1]) in (MessageDownloadJob, ReplyDownloadJob), self.queue)
        )
        return len(message_and_reply_download_jobs)


class RunnableQueue(QObject):
    """
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
    job and continue on to processing the next job. The job itself is responsible for emitting the
    success and failure signals, so when an unexpected error occurs, it should emit the failure
    signal so that the Controller can respond accordingly.
    """

    # These are the priorities for processing jobs. Lower numbers corresponds to a higher priority.
    JOB_PRIORITIES = {
        ClearQueueJob: 0,  # Must preempt all other jobs
        PauseQueueJob: 11,
        FileDownloadJob: 13,  # File downloads processed in separate queue
        DeleteSourceJob: 14,
        DeleteConversationJob: 14,
        SendReplyJob: 15,
        UpdateStarJob: 16,
        MessageDownloadJob: 17,
        ReplyDownloadJob: 17,
        SeenJob: 18,
    }

    # Signal that is emitted when processing is stopped and queued jobs are cleared
    cleared = pyqtSignal()

    # Signal that is emitted when processing is paused
    paused = pyqtSignal()

    # Signal that is emitted to resume processing jobs
    resume = pyqtSignal()

    def __init__(
        self,
        api_client: API,
        session_maker: scoped_session,
        queue_updated_signal: Optional[pyqtBoundSignal] = None,
    ) -> None:
        super().__init__()
        self.api_client = api_client
        self.session_maker = session_maker
        self.queue = RunnablePriorityQueue(
            queue_updated_signal=queue_updated_signal
        )  # type: PriorityQueue[Tuple[int, QueueJob]]
        # `order_number` ensures jobs with equal priority are retrieved in FIFO order. This is
        # needed because PriorityQueue is implemented using heapq which does not have sort
        # stability. For more info, see : https://bugs.python.org/issue17794
        self.order_number = itertools.count()
        self.current_job = None  # type: Optional[QueueJob]

        # Hold when reading/writing self.current_job or mutating queue state
        self.condition_add_or_remove_job = threading.Condition()

        self.resume.connect(self.process)

    def _check_for_duplicate_jobs(self, job: QueueJob) -> bool:
        """
        Queued jobs are stored on self.queue.queue. The currently executing job is
        stored on self.current_job. We check that the job to be added is not among them.
        """
        in_progress_jobs = [in_progress_job for priority, in_progress_job in self.queue.queue]
        if self.current_job is not None:
            in_progress_jobs.append(self.current_job)
        if job in in_progress_jobs:
            logger.debug("Duplicate job {}, skipping".format(job))
            return True
        return False

    def _clear(self) -> None:
        """
        Reinstantiate the PriorityQueue, rather than trying to clear it via undocumented methods.[1]

        [1]: https://stackoverflow.com/a/38560911
        """
        with self.condition_add_or_remove_job:
            self.queue = PriorityQueue()
        self.cleared.emit()

    def add_job(self, job: QueueJob) -> None:
        """
        Add the job with its priority to the queue after assigning it the next order_number.

        Can block while waiting to acquire condition_add_or_remove_job.
        """
        with self.condition_add_or_remove_job:
            if self._check_for_duplicate_jobs(job):
                return

            logger.debug("Added {} to queue".format(job))
            current_order_number = next(self.order_number)
            job.order_number = current_order_number
            priority = self.JOB_PRIORITIES[type(job)]
            self.queue.put_nowait((priority, job))
            self.condition_add_or_remove_job.notify()

    def _re_add_job(self, job: QueueJob) -> None:
        """
        Reset the job's remaining attempts and put it back into the queue in the order in which it
        was submitted by the user (do not assign it the next order_number). Used internally.

        When called condition_add_or_remove_job should be held.
        """
        if self._check_for_duplicate_jobs(job):
            return

        logger.debug("Added {} to queue".format(job))
        job.remaining_attempts = DEFAULT_NUM_ATTEMPTS
        priority = self.JOB_PRIORITIES[type(job)]
        self.queue.put_nowait((priority, job))
        self.condition_add_or_remove_job.notify()

    @pyqtSlot()
    def process(self) -> None:
        """
        Process the next job in the queue.

        If the job is a ClearQueueJob, call _clear() and return from the processing loop so that
        the processing thread can quit.

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
        """
        while True:
            with self.condition_add_or_remove_job:
                self.condition_add_or_remove_job.wait_for(lambda: not self.queue.empty())
                priority, self.current_job = self.queue.get(block=False)

            if isinstance(self.current_job, ClearQueueJob):
                with self.condition_add_or_remove_job:
                    self.current_job = None
                self._clear()
                return

            if isinstance(self.current_job, PauseQueueJob):  # type: ignore
                self.paused.emit()
                with self.condition_add_or_remove_job:
                    self.current_job = None
                return

            try:
                if isinstance(self.current_job, ApiJob):
                    session = self.session_maker()
                    self.current_job._do_call_api(self.api_client, session)
            except ApiInaccessibleError as e:
                logger.debug("{}: {}".format(type(e).__name__, e))
                self.api_client = None
                with self.condition_add_or_remove_job:
                    self.current_job = None
                return
            except (RequestTimeoutError, ServerConnectionError) as e:
                logger.debug("{}: {}".format(type(e).__name__, e))
                self.add_job(PauseQueueJob())
                with self.condition_add_or_remove_job:
                    job, self.current_job = self.current_job, None
                    self._re_add_job(job)
            except Exception as e:
                logger.error("Skipping job")
                logger.debug(f"Skipping job: {type(e).__name__}: {e}")
            finally:
                with self.condition_add_or_remove_job:
                    self.current_job = None
                session.close()


class ApiJobQueue(QObject):
    """
    ApiJobQueue is the queue manager of two FIFO priority queues that process jobs of type ApiJob.


    The queue manager starts the queues when a new auth token is provided to ensure jobs are able to
    make their requests. It stops the queues whenever a MetadataSyncJob, which runs in a continuous
    loop outside of the queue manager, encounters an ApiInaccessibleError and forces a logout
    from the Controller.
    """

    # Signal that is emitted after a queue is cleared.
    cleared = pyqtSignal()

    # Signal that is emitted after a queue is paused.
    paused = pyqtSignal()

    # Signal emitted when an item is added or removed from the main queue
    main_queue_updated = pyqtSignal(int)

    def __init__(
        self,
        api_client: API,
        session_maker: scoped_session,
        main_thread: QThread,
        download_file_thread: QThread,
    ) -> None:
        super().__init__(None)

        self.main_thread = main_thread
        self.download_file_thread = download_file_thread

        self.main_queue = RunnableQueue(
            api_client, session_maker, queue_updated_signal=self.main_queue_updated
        )
        self.download_file_queue = RunnableQueue(api_client, session_maker)

        self.main_queue.moveToThread(self.main_thread)
        self.download_file_queue.moveToThread(self.download_file_thread)

        self.main_thread.started.connect(self.main_queue.process)
        self.download_file_thread.started.connect(self.download_file_queue.process)

        self.main_queue.paused.connect(self.on_main_queue_paused)
        self.download_file_queue.paused.connect(self.on_file_download_queue_paused)

        self.main_queue.cleared.connect(self.on_main_queue_cleared)
        self.download_file_queue.cleared.connect(self.on_file_download_queue_cleared)

    def start(self, api_client: API) -> None:
        """
        Start the queues whenever a new api token is provided.
        """
        self.main_queue.api_client = api_client
        self.download_file_queue.api_client = api_client

        if not self.main_thread.isRunning():
            self.main_thread.start()
            logger.debug("Started main queue")

        if not self.download_file_thread.isRunning():
            self.download_file_thread.start()
            logger.debug("Started file download queue")

    def stop(self) -> None:
        """
        Inject a ClearQueueJob into each queue and quit its processing thread.  To keep this
        method non-blocking, we do NOT wait() for the thread to return, which will happen only
        when RunnableQueue.process() reaches the ClearQueueJob and returns from its loop.
        """
        if self.main_thread.isRunning():
            self.main_queue.add_job(ClearQueueJob())
            self.main_thread.quit()
            logger.debug("Asked main queue thread to quit")

        if self.download_file_thread.isRunning():
            self.download_file_queue.add_job(ClearQueueJob())
            self.download_file_thread.quit()
            logger.debug("Asked file-download queue thread to quit")

    @pyqtSlot()
    def on_main_queue_paused(self) -> None:
        """
        Emit the paused signal if the main queue has been paused.
        """
        logger.debug("Paused main queue")
        self.paused.emit()

    @pyqtSlot()
    def on_file_download_queue_paused(self) -> None:
        """
        Emit the paused signal if the file download queue has been paused.
        """
        logger.debug("Paused file download queue")
        self.paused.emit()

    @pyqtSlot()
    def on_main_queue_cleared(self) -> None:
        """
        Emit the "cleared" signal when the main RunnableQueue is cleared.
        """
        logger.debug("Cleared main queue")
        self.cleared.emit()

    @pyqtSlot()
    def on_file_download_queue_cleared(self) -> None:
        """
        Emit the "cleared" signal when the file-download RunnableQueue is cleared.
        """
        logger.debug("Cleared file download queue")
        self.cleared.emit()

    def resume_queues(self) -> None:
        """
        Emit the resume signal to the queues if they are running.
        """
        if self.main_thread.isRunning():
            logger.debug("Resuming main queue")
            self.main_queue.resume.emit()
        if self.download_file_thread.isRunning():
            logger.debug("Resuming download queue")
            self.download_file_queue.resume.emit()

    @pyqtSlot(object)
    def enqueue(self, job: ApiJob) -> None:
        """
        Enqueue the supplied job if the queues are running.
        """
        if not self.main_thread.isRunning() or not self.download_file_thread.isRunning():
            logger.debug("Not adding job before queues have been started.")
            return

        if isinstance(job, FileDownloadJob):
            self.download_file_queue.add_job(job)
        else:
            self.main_queue.add_job(job)
