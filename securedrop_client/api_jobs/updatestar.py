import logging
import sdclientapi

from sdclientapi import API, RequestTimeoutError, ServerConnectionError
from sqlalchemy.orm.session import Session

from securedrop_client.api_jobs.base import ApiJob

logger = logging.getLogger(__name__)


class UpdateStarJob(ApiJob):
    def __init__(self, source_uuid: str, is_starred: bool) -> None:
        super().__init__()
        self.source_uuid = source_uuid
        self.is_starred = is_starred

    def call_api(self, api_client: API, session: Session) -> str:
        '''
        Override ApiJob.

        Star or Unstar an user on the server
        '''
        try:
            source_sdk_object = sdclientapi.Source(uuid=self.source_uuid)

            if self.is_starred:
                api_client.remove_star(source_sdk_object)
            else:
                api_client.add_star(source_sdk_object)

            return self.source_uuid
        except (RequestTimeoutError, ServerConnectionError) as e:
            error_message = f'Failed to update star on source {self.source_uuid} due to error: {e}'
            raise UpdateStarJobTimeoutError(error_message, self.source_uuid)
        except Exception as e:
            error_message = f'Failed to update star on source {self.source_uuid} due to {e}'
            raise UpdateStarJobError(error_message, self.source_uuid)


class UpdateStarJobError(Exception):
    def __init__(self, message: str, source_uuid: str) -> None:
        super().__init__(message)
        self.source_uuid = source_uuid


class UpdateStarJobTimeoutError(RequestTimeoutError):
    def __init__(self, message: str, source_uuid: str) -> None:
        super().__init__()
        self.message = message
        self.source_uuid = source_uuid

    def __str__(self) -> str:
        return self.message
