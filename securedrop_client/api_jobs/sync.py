import logging
from typing import Any, Callable, List, Union

from sdclientapi import API
from sqlalchemy.orm.session import Session

from securedrop_client import state
from securedrop_client.api_jobs.base import ApiJob
from securedrop_client.storage import (
    create_or_update_user,
    get_file,
    get_remote_data,
    update_local_storage,
)

logger = logging.getLogger(__name__)


class MetadataSyncJob(ApiJob):
    """
    Update source metadata such that new download jobs can be added to the queue.
    """

    NUMBER_OF_TIMES_TO_RETRY_AN_API_CALL = 2

    def __init__(self, data_dir: str, gui_state: state.State) -> None:
        super().__init__(remaining_attempts=self.NUMBER_OF_TIMES_TO_RETRY_AN_API_CALL)
        self.data_dir = data_dir
        self._state = gui_state

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
        sources, submissions, replies = get_remote_data(api_client)

        update_local_storage(session, sources, submissions, replies, self.data_dir)

        _update_state(
            self._state,
            sources,
            submissions,
            get_file_from_local_storage=lambda submission_id: get_file(session, submission_id),
        )

        user = api_client.get_current_user()
        if "uuid" in user and "username" in user and "first_name" in user and "last_name" in user:
            create_or_update_user(
                user["uuid"], user["username"], user["first_name"], user["last_name"], session
            )


def _update_state(
    app_state: state.State,
    sources: List,
    submissions: List,
    get_file_from_local_storage: Callable[[Any], Any],
) -> None:
    for source in sources:
        source_id = source.uuid
        files: List[Union[state.FileId, state.DownloadedFileId]] = []
        for submission in submissions:
            submission_id = submission.uuid
            if submission.source_uuid == source_id and submission.is_file():
                file = get_file_from_local_storage(submission_id)
                if file.is_downloaded:
                    files.append(state.DownloadedFileId(submission_id))
                else:
                    files.append(state.FileId(submission_id))

        conversation_id = source_id
        app_state.update_or_insert_conversation(conversation_id, files)
