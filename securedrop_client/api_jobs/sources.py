import logging
import sdclientapi

from sdclientapi import API
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
        source_sdk_object = sdclientapi.Source(uuid=self.source_uuid)

        # TODO: After https://github.com/freedomofpress/securedrop-client/issues/648 is merged, we
        # will want to pass the timeout to delete_source instead of setting it on the api object
        api_client.default_request_timeout = 5
        api_client.delete_source(source_sdk_object)

        return self.source_uuid
