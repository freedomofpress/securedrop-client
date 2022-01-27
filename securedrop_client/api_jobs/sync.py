import logging
from typing import Any, List

from sdclientapi import API
from sqlalchemy.orm.session import Session

from securedrop_client.api_jobs.base import ApiInaccessibleError, ApiJob
from securedrop_client.db import User
from securedrop_client.storage import get_remote_data, update_local_storage

logger = logging.getLogger(__name__)


class MetadataSyncJob(ApiJob):
    """
    Update source metadata such that new download jobs can be added to the queue.
    """

    NUMBER_OF_TIMES_TO_RETRY_AN_API_CALL = 2

    def __init__(self, data_dir: str) -> None:
        super().__init__(remaining_attempts=self.NUMBER_OF_TIMES_TO_RETRY_AN_API_CALL)
        self.data_dir = data_dir

    def call_api(self, api_client: API, session: Session) -> Any:
        """
        Override ApiJob.

        Download new metadata, update the local database, import new keys, and
        then the success signal will let the controller know to add any new download
        jobs.
        """

        # TODO: Once https://github.com/freedomofpress/securedrop-client/issues/648, we will want to
        # pass the default request timeout to api calls instead of setting it on the api object
        # directly.
        #
        # This timeout is used for 3 different requests: `get_sources`, `get_all_submissions`, and
        # `get_all_replies`
        api_client.default_request_timeout = 60
        user = api_client.get_current_user()
        if not user:
            raise ApiInaccessibleError()
        users = api_client.get_users()
        MetadataSyncJob._update_users(session, users)
        sources, submissions, replies = get_remote_data(api_client)
        update_local_storage(session, sources, submissions, replies, self.data_dir)

    def _update_users(session: Session, remote_users: List[User]) -> None:
        """
        1. Create local user accounts for each remote user that doesn't already exist
        2. Update existing local users
        3. Delete all remaining local user accounts that no longer exist on the server
        """
        local_users = {user.uuid: user for user in session.query(User).all()}
        for remote_user in remote_users:
            local_user = local_users.get(remote_user.uuid)
            if not local_user:
                new_user = User(
                    uuid=remote_user.uuid,
                    username=remote_user.username,
                    firstname=remote_user.first_name,
                    lastname=remote_user.last_name,
                )
                session.add(new_user)
                logger.debug(f"Adding account for user {new_user.uuid}")
            else:
                if local_user.username != remote_user.username:
                    local_user.username = remote_user.username
                if local_user.firstname != remote_user.first_name:
                    local_user.firstname = remote_user.first_name
                if local_user.lastname != remote_user.last_name:
                    local_user.lastname = remote_user.last_name
                del local_users[remote_user.uuid]

        for uuid, account in local_users.items():
            session.delete(account)
            logger.debug(f"Deleting account for user {uuid}")

        session.commit()
