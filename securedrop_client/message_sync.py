"""
Contains the MessageSync class, which runs in the background and loads new
 messages from the SecureDrop server.

Copyright (C) 2018  The Freedom of the Press Foundation.

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published
by the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
"""

import time
import logging
from PyQt5.QtCore import QObject
from securedrop_client import storage

from sqlalchemy.orm import sessionmaker
from securedrop_client.models import engine


logger = logging.getLogger(__name__)


class MessageSync(QObject):
    """
    Runs in the background, finding messages to download and downloading them.
    """

    def __init__(self, api):
        super().__init__()
        Session = sessionmaker(bind=engine)
        self.session = Session() # Reference to the SqlAlchemy session.
        self.api = api

    def run(self):
        while True:
            logger.info("Fetching messages...")
            submissions = storage.find_new_submissions(self.session)

            for m in submissions:
                logger.info("Downloading {}".format(m.download_url))
                shasum, filepath = self.api.download_submission_from_url(m.download_url)
                logger.info("Downloaded {}".format(filepath))
                # jt you are here... put that all in a try/except
                # then try to decrypt
                # then store the actual message on disk somewhere?
                # then mark as downloaded in the db
            time.sleep(5)
