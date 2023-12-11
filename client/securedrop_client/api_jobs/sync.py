import logging
import os
from typing import Any, List, Optional

from sdclientapi import API
from sdclientapi import User as SDKUser
from sqlalchemy.orm.session import Session

from securedrop_client import state
from securedrop_client.api_jobs.base import ApiJob
from securedrop_client.db import DeletedUser, DraftReply, User
from securedrop_client.storage import get_remote_data, update_local_storage

logger = logging.getLogger(__name__)


class MetadataSyncJob(ApiJob):
    """
    Update source metadata such that new download jobs can be added to the queue.
    """

    DEFAULT_REQUEST_TIMEOUT = 60  # sec
    NUMBER_OF_TIMES_TO_RETRY_AN_API_CALL = 2

    def __init__(self, data_dir: str, app_state: Optional[state.State] = None) -> None:
        super().__init__(remaining_attempts=self.NUMBER_OF_TIMES_TO_RETRY_AN_API_CALL)
        self.data_dir = data_dir
        self._state = app_state

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
        api_client.default_request_timeout = int(
            os.environ.get("SDEXTENDEDTIMEOUT", self.DEFAULT_REQUEST_TIMEOUT)
        )
        if api_client.default_request_timeout != self.DEFAULT_REQUEST_TIMEOUT:
            logger.warn(
                f"{self.__class__.__name__} will use "
                f"default_request_timeout={api_client.default_request_timeout}"
            )

        users = api_client.get_users()
        MetadataSyncJob._update_users(session, users)
        sources, submissions, replies = get_remote_data(api_client)
        update_local_storage(session, sources, submissions, replies, self.data_dir)
        if self._state is not None:
            _update_state(self._state, submissions)

    def _update_users(session: Session, remote_users: List[SDKUser]) -> None:
        """
        1. Create local user accounts for each remote user that doesn't already exist
        2. Update existing local users
        3. Re-associate any draft replies sent by a user that is about to be deleted
        4. Delete all remaining local user accounts that no longer exist on the server
        """
        deleted_user_id = None  # type: Optional[int]
        local_users = {user.uuid: user for user in session.query(User).all()}
        for remote_user in remote_users:
            local_user = local_users.get(remote_user.uuid)
            if not local_user:  # Create local user account
                new_user = User(
                    uuid=remote_user.uuid,
                    username=remote_user.username,
                    firstname=remote_user.first_name,
                    lastname=remote_user.last_name,
                )
                session.add(new_user)

                # If the new user is the "deleted" user account, store its id in case we need to
                # reassociate draft replies later.
                if new_user.deleted:
                    session.commit()
                    deleted_user_id = new_user.id

                logger.debug(f"Adding account for user with uuid='{new_user.uuid}'")
            else:  # Update existing local users
                # If the local user is the "deleted" user account, store its id in case we need to
                # reassociate draft replies later.
                if local_user.deleted:
                    deleted_user_id = local_user.id

                if local_user.username != remote_user.username:
                    local_user.username = remote_user.username
                if local_user.firstname != remote_user.first_name:
                    local_user.firstname = remote_user.first_name
                if local_user.lastname != remote_user.last_name:
                    local_user.lastname = remote_user.last_name
                del local_users[remote_user.uuid]

        # Delete all remaining local user accounts that no longer exist on the server.
        #
        # In order to support an edge case that can occur on a pre-2.2.0 server that does not create
        # a "deleted" user account, the client will create one locally when there are draft replies
        # that need to be re-associated. Once the "deleted" user account exists on the server, it
        # will replace the local one.
        for uuid, account in local_users.items():
            # Do not delete the local "deleted" user account if there is no "deleted" user account
            # on the server.
            if account.deleted and not deleted_user_id:
                continue

            # Get draft replies sent by the user who's account is about to be deleted.
            draft_replies = session.query(DraftReply).filter_by(journalist_id=account.id).all()

            # Create a local "deleted" user account if there is no "deleted" user account locally or
            # on the server and we are about to delete a user.
            if draft_replies and not account.deleted and not deleted_user_id:
                deleted_user = DeletedUser()
                session.add(deleted_user)
                session.commit()  # commit so that we can retrieve the generated `id`
                deleted_user_id = deleted_user.id
                logger.debug(f"Creating DeletedUser with uuid='{deleted_user.uuid}'")

            # Re-associate draft replies
            for reply in draft_replies:
                reply.journalist_id = deleted_user_id
                logger.debug(f"DraftReply with uuid='{reply.uuid}' re-associated to DeletedUser")

            # Ensure re-associated draft replies are committed to the db before deleting the account
            if draft_replies:
                session.commit()

            session.delete(account)
            logger.debug(f"Deleting account for user with uuid='{uuid}'")

        session.commit()


def _update_state(app_state: state.State, submissions: List) -> None:
    for submission in submissions:
        if submission.is_file():
            app_state.add_file(
                state.ConversationId(submission.source_uuid), state.FileId(submission.uuid)
            )
