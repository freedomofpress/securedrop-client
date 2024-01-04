from typing import List

from sqlalchemy.orm.session import Session

from securedrop_client.api_jobs.base import ApiJob
from securedrop_client.sdk import API


class SeenJob(ApiJob):
    def __init__(self, files: List[str], messages: List[str], replies: List[str]) -> None:
        super().__init__()
        self.files = files
        self.messages = messages
        self.replies = replies

    def call_api(self, api_client: API, session: Session) -> None:
        """
        Override ApiJob.

        Mark files, messages, and replies as seen. Do not make the request if there are no items to
        be marked as seen.
        """
        if not self.files and not self.messages and not self.replies:
            return

        api_client.seen(self.files, self.messages, self.replies)
