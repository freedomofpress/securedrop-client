import logging

from sqlalchemy.orm.session import Session

from securedrop_client import sdk
from securedrop_client.api_jobs.base import SingleObjectApiJob
from securedrop_client.sdk import API, RequestTimeoutError, ServerConnectionError

logger = logging.getLogger(__name__)


class UpdateStarJob(SingleObjectApiJob):
    def __init__(self, uuid: str, is_starred: bool) -> None:
        super().__init__(uuid)
        self.is_starred = is_starred

    def call_api(self, api_client: API, session: Session) -> str:
        """
        Override ApiJob.

        Star or Unstar an user on the server
        """
        try:
            source_sdk_object = sdk.Source(uuid=self.uuid)

            if self.is_starred:
                api_client.remove_star(source_sdk_object)
            else:
                api_client.add_star(source_sdk_object)

            return self.uuid
        except (RequestTimeoutError, ServerConnectionError) as e:
            error_message = f"Failed to update star on source {self.uuid} due to error: {e}"
            raise UpdateStarJobTimeoutError(error_message, self.uuid)
        except Exception as e:
            error_message = f"Failed to update star on source {self.uuid} due to {e}"
            raise UpdateStarJobError(error_message, self.uuid)


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
