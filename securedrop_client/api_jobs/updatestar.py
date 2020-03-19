import logging
import sdclientapi

from typing import Tuple

from sdclientapi import API
from sqlalchemy.orm.session import Session

from securedrop_client.api_jobs.base import ApiJob

logger = logging.getLogger(__name__)


class UpdateStarJob(ApiJob):
    def __init__(self, source_uuid: str, is_starred: bool) -> None:
        super().__init__()
        self.source_uuid = source_uuid
        self.is_starred = is_starred

    def call_api(self, api_client: API, session: Session) -> Tuple[str, bool]:
        '''
        Override ApiJob.

        Star or Unstar an user on the server
        '''
        try:
            source_sdk_object = sdclientapi.Source(uuid=self.source_uuid)

            # TODO: Once https://github.com/freedomofpress/securedrop-client/issues/648, we will
            # want to pass the default request timeout to remove_star and add_star instead of
            # setting it on the api object directly.
            api_client.default_request_timeout = 5
            if self.is_starred:
                api_client.remove_star(source_sdk_object)
            else:
                api_client.add_star(source_sdk_object)

            # Identify the source and *new* state of the star so the UI can be
            # updated.
            return self.source_uuid, not self.is_starred
        except Exception as e:
            error_message = "Failed to update star on source {uuid} due to {exception}".format(
                uuid=self.source_uuid, exception=repr(e))
            raise UpdateStarJobException(error_message, self.source_uuid, self.is_starred)


class UpdateStarJobException(Exception):
    def __init__(self, message: str, source_uuid: str, is_starred: bool) -> None:
        super().__init__(message)
        self.source_uuid = source_uuid
        self.is_starred = is_starred
