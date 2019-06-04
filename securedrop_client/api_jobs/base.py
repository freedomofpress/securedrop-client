import logging

from PyQt5.QtCore import QObject, pyqtSignal
from sdclientapi import API, RequestTimeoutError, AuthError
from sqlalchemy.orm.session import Session
from typing import Any, Optional


logger = logging.getLogger(__name__)


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

    def __init__(self) -> None:
        super().__init__(None)  # `None` because the QOjbect has no parent

    def _do_call_api(self, api_client: API, session: Session) -> None:
        if not api_client:
            raise ApiInaccessibleError()

        try:
            result = self.call_api(api_client, session)
        except AuthError as e:
            raise ApiInaccessibleError() from e
        except RequestTimeoutError:
            logger.debug('Job {} timed out'.format(self))
            raise
        except Exception as e:
            logger.error('Job {} raised an exception: {}: {}'
                         .format(self, type(e).__name__, e))
            self.failure_signal.emit(e)
        else:
            self.success_signal.emit(result)

    def call_api(self, api_client: API, session: Session) -> Any:
        '''
        Method for making the actual API call and handling the result.

        This MUST resturn a value if the API call and other tasks were successful and MUST raise
        an exception if and only iff the tasks failed. Presence of a raise exception indicates a
        failure.
        '''
        raise NotImplementedError
