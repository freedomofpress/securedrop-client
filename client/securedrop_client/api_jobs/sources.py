import logging

from sqlalchemy.orm.session import Session

from securedrop_client import sdk
from securedrop_client.api_jobs.base import ApiJob
from securedrop_client.sdk import API, RequestTimeoutError, ServerConnectionError

logger = logging.getLogger(__name__)


class DeleteSourceJob(ApiJob):
    def __init__(self, uuid: str) -> None:
        super().__init__()
        self.uuid = uuid

    def call_api(self, api_client: API, session: Session) -> str:
        """
        Override ApiJob.

        Delete a source on the server
        """
        try:
            source_sdk_object = sdk.Source(uuid=self.uuid)
            api_client.delete_source(source_sdk_object)

            return self.uuid
        except (RequestTimeoutError, ServerConnectionError):
            raise
        except Exception as e:
            error_message = f"Failed to delete source {self.uuid} due to {repr(e)}"
            raise DeleteSourceJobException(error_message, self.uuid)


class DeleteConversationJob(ApiJob):
    def __init__(self, uuid: str) -> None:
        super().__init__()
        self.uuid = uuid

    def call_api(self, api_client: API, session: Session) -> str:
        """
        Override ApiJob.

        Delete a source on the server
        """
        try:
            api_client.delete_conversation(uuid=self.uuid)
            return self.uuid
        except (RequestTimeoutError, ServerConnectionError):
            raise
        except Exception as e:
            error_message = f"Failed to delete conversation for source {self.uuid}: {repr(e)}"
            raise DeleteConversationJobException(error_message, self.uuid)


class DeleteConversationJobException(Exception):
    def __init__(self, message: str, source_uuid: str):
        super().__init__(message)
        self.source_uuid = source_uuid


class DeleteSourceJobException(Exception):
    def __init__(self, message: str, source_uuid: str):
        super().__init__(message)
        self.source_uuid = source_uuid
