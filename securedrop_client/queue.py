import logging
import sdclientapi

from PyQt5.QtCore import QObject, QThread, pyqtSignal, pyqtBoundSignal
from queue import Queue
from sdclientapi import API, RequestTimeoutError
from typing import Any, Optional, Union

from securedrop_client.db import File, Message


logger = logging.getLogger(__name__)


class ApiJob:

    def __init__(self, nargs: list, kwargs: dict) -> None:
        self.nargs = nargs
        self.kwargs = kwargs

    def _do_call_api(self, api_client: API) -> None:
        try:
            result = self.call_api(api_client, self.nargs, self.kwargs)
        except RequestTimeoutError:
            logger.debug('Job {} timed out'.format(self))
            raise
        except Exception as e:
            logger.error('Job {} raised an exception: {}'.format(self, e))
            self.handle_failure(e)
        else:
            self.handle_success(result)

    def call_api(self, api_client: API, nargs: list, kwargs: dict) -> Any:
        raise NotImplementedError

    def handle_success(self, result: Any) -> None:
        raise NotImplementedError

    def handle_failure(self, exception: Exception) -> None:
        raise NotImplementedError


class DownloadSubmissionJob(ApiJob):

    def __init__(
        self,
        submission: sdclientapi.Submission,
        data_dir: str,
        db_object: Union[File, Message],
    ) -> None:
        super().__init__([submission, data_dir], {})
        self.__db_object = db_object

    def call_api(self, api_client: API, nargs: list, kwargs: dict) -> Any:
        return api_client.download_submission(*nargs, **kwargs)


class RunnableQueue(QObject):

    def __init__(self, api_client: API, halt_signal: pyqtBoundSignal) -> None:
        super().__init__()
        self.run = True
        self.api_client = api_client
        self.queue = Queue()  # type: Queue[ApiJob]

        self.halt_signal = halt_signal
        halt_signal.connect(self.stop)

    def stop(self) -> None:
        self.run = False

    def __call__(self, loop: bool = True) -> None:
        while self.run:
            job = self.queue.get(block=True)  # type: ApiJob

            try:
                job._do_call_api(self.api_client)
            except RequestTimeoutError:
                self.run = False
                self.halt_signal.emit()  # notify other threads of failure
                return

            if not loop:
                return


class ApiJobQueue(QObject):

    '''
    Signal used to notify different job threads that they should halt. This is pub/sub like signal
    in that any threat may trigger it, and all threads listen to it.
    '''
    halt_signal = pyqtSignal()

    def __init__(self, api_client: API, parent: Optional[QObject] = None) -> None:
        super().__init__(parent)
        self.api_client = api_client
        self.main_queue = RunnableQueue(self.api_client, self.halt_signal)
        self.download_queue = RunnableQueue(self.api_client, self.halt_signal)

    def start_queues(self) -> None:
        # ensure the queues are set to run (for previously stopped threads)
        self.main_queue.run = True
        self.download_queue.run = True

        main_thread = QThread(self)
        download_thread = QThread(self)

        self.main_queue.moveToThread(main_thread)
        self.download_queue.moveToThread(download_thread)

        main_thread.run()
        download_thread.run()

    def enqueue(self, job: ApiJob) -> None:
        if isinstance(job, DownloadSubmissionJob):
            self.download_queue.queue.put_nowait(job)
        else:
            self.main_queue.queue.put_nowait(job)
