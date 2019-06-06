import logging

from PyQt5.QtCore import QObject, QThread, pyqtSlot
from PyQt5.QtWidgets import QApplication
from queue import Queue
from sdclientapi import API, RequestTimeoutError
from sqlalchemy.orm import scoped_session
from typing import Optional  # noqa: F401

from securedrop_client.api_jobs.base import ApiJob
from securedrop_client.api_jobs.downloads import FileDownloadJob, MessageDownloadJob


logger = logging.getLogger(__name__)


class RunnableQueue(QObject):

    def __init__(self, api_client: API, session_maker: scoped_session) -> None:
        super().__init__()
        self.api_client = api_client
        self.session_maker = session_maker
        self.queue = Queue()  # type: Queue[ApiJob]
        self.last_job = None  # type: Optional[ApiJob]

    @pyqtSlot()
    def process(self) -> None:  # pragma: nocover
        self._process(False)

    def _process(self, exit_loop: bool) -> None:
        session = self.session_maker()
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

    def __init__(self, api_client: API, session_maker: scoped_session) -> None:
        super().__init__(None)
        self.api_client = api_client

        self.main_thread = QThread()
        self.download_thread = QThread()

        self.main_queue = RunnableQueue(self.api_client, session_maker)
        self.download_queue = RunnableQueue(self.api_client, session_maker)

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
        if isinstance(job, FileDownloadJob):
            self.download_queue.queue.put_nowait(job)
        else:
            self.main_queue.queue.put_nowait(job)
