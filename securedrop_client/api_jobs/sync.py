from typing import Any
import logging

from sdclientapi import API
from sqlalchemy.orm.session import Session

from securedrop_client.api_jobs.base import ApiJob
from securedrop_client.crypto import GpgHelper
from securedrop_client.storage import get_remote_data, update_local_storage


logger = logging.getLogger(__name__)


class MetadataSyncJob(ApiJob):
    '''
    Update source metadata such that new download jobs can be added to the queue.
    '''

    def __init__(self, data_dir: str, gpg: GpgHelper) -> None:
        super().__init__()
        self.data_dir = data_dir
        self.gpg = gpg

    def call_api(self, api_client: API, session: Session) -> Any:
        '''
        Override ApiJob.

        Download new metadata, update the local database, import new keys, and
        then the success signal will let the controller know to add any new download
        jobs.
        '''

        # TODO: Once https://github.com/freedomofpress/securedrop-client/issues/648, we will want to
        # pass the default request timeout to api calls instead of setting it on the api object
        # directly.
        api_client.default_request_timeout = 40
        remote_sources, remote_submissions, remote_replies = get_remote_data(api_client)

        update_local_storage(session,
                             self.gpg,
                             remote_sources,
                             remote_submissions,
                             remote_replies,
                             self.data_dir)
