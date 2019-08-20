import logging

from PyQt5.QtCore import QObject, pyqtSignal
from sdclientapi import API, AuthError, RequestTimeoutError
from sqlalchemy.orm.session import Session
from typing import Any, Optional, TypeVar

logger = logging.getLogger(__name__)

DEFAULT_NUM_ATTEMPTS = 5

ApiJobType = TypeVar('ApiJobType', bound='ApiJob')


class ApiInaccessibleError(Exception):

    def __init__(self, message: Optional[str] = None) -> None:
        if not message:
            message = ('API is inaccessible either because there is no client or because the '
                       'client is not properly authenticated.')
        super().__init__(message)


class ApiJob(QObject):

    '''
    Signal that is emitted after an job finishes successfully.
    '''
    success_signal = pyqtSignal('PyQt_PyObject')

    '''
    Signal that is emitted if there is a failure during the job.
    '''
    failure_signal = pyqtSignal(Exception)

    def __init__(self, remaining_attempts: int = DEFAULT_NUM_ATTEMPTS) -> None:
        super().__init__(None)  # `None` because the QOjbect has no parent
        self.remaining_attempts = remaining_attempts
        self.order_number = None  # type: Optional[int]

    def __lt__(self, other: ApiJobType) -> bool:
        '''
        Python's PriorityQueue requires that ApiJobs are sortable as it
        retrieves the next job using sorted(list(entries))[0].

        For ApiJobs that have equal priority, we need to use the order_number key
        to break ties to ensure that objects are retrieved in FIFO order.
        '''
        if self.order_number is None or other.order_number is None:
            raise ValueError('cannot compare jobs without order_number!')

        return self.order_number < other.order_number

    def _do_call_api(self, api_client: API, session: Session) -> None:
        if not api_client:
            raise ApiInaccessibleError()

        while self.remaining_attempts >= 1:
            try:
                self.remaining_attempts -= 1
                result = self.call_api(api_client, session)
            except (ApiInaccessibleError, AuthError) as e:
                raise ApiInaccessibleError() from e
            except RequestTimeoutError as e:
                if self.remaining_attempts == 0:
                    self.failure_signal.emit(e)
                    raise
            except Exception as e:
                self.failure_signal.emit(e)
                raise
            else:
                self.success_signal.emit(result)
                break

    def call_api(self, api_client: API, session: Session) -> Any:
        '''
        Method for making the actual API call and handling the result.

        This MUST resturn a value if the API call and other tasks were successful and MUST raise
        an exception if and only if the tasks failed. Presence of a raise exception indicates a
        failure.
        '''
        raise NotImplementedError
