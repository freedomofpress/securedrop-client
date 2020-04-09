import logging
import sdclientapi

from sdclientapi import API, ServerConnectionError, RequestTimeoutError
from sqlalchemy.orm.session import Session

from securedrop_client.api_jobs.base import ApiJob

logger = logging.getLogger(__name__)


class DeleteSourceJob(ApiJob):
    def __init__(self, source_uuid: str) -> None:
        super().__init__()
        self.source_uuid = source_uuid

    def call_api(self, api_client: API, session: Session) -> str:
        '''
        Override ApiJob.

        Delete a source on the server
        '''
        try:
            source_sdk_object = sdclientapi.Source(uuid=self.source_uuid)
            api_client.delete_source(source_sdk_object)

            return self.source_uuid
        except (RequestTimeoutError, ServerConnectionError):
            raise
        except Exception as e:
            error_message = "Failed to delete source {uuid} due to {exception}".format(
                uuid=self.source_uuid, exception=repr(e))
            raise DeleteSourceJobException(error_message, self.source_uuid)


class DeleteSourceJobException(Exception):
    def __init__(self, message: str, source_uuid: str):
        super().__init__(message)
        self.source_uuid = source_uuid
