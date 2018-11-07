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
import os
import shutil
import subprocess
import tempfile
import sdclientapi.sdlocalobjects as sdkobjects

from PyQt5.QtCore import QObject
from securedrop_client import storage
from securedrop_client.models import make_engine

from sqlalchemy.orm import sessionmaker


logger = logging.getLogger(__name__)


class APISyncObject(QObject):

    def __init__(self, api, home, is_qubes):
        super().__init__()

        engine = make_engine(home)
        Session = sessionmaker(bind=engine)
        self.session = Session()  # Reference to the SqlAlchemy session.
        self.api = api
        self.home = home
        self.is_qubes = is_qubes

    def fetch_the_thing(self, item, msg, download_fn, update_fn):
        shasum, filepath = download_fn(item)

        out = tempfile.NamedTemporaryFile(suffix=".message")
        err = tempfile.NamedTemporaryFile(suffix=".message-error",
                                          delete=False)

        if self.is_qubes:
            gpg_binary = "qubes-gpg-client"
        else:
            gpg_binary = "gpg"

        cmd = [gpg_binary, "--decrypt", filepath]
        res = subprocess.call(cmd, stdout=out, stderr=err)
        os.unlink(filepath)

        if res != 0:
            out.close()
            err.close()

            with open(err.name) as e:
                msg = e.read()
                logger.error("GPG error: {}".format(msg))
                os.unlink(err.name)

        else:
            fn_no_ext, _ = os.path.splitext(msg.filename)
            dest = os.path.join(self.home, "data", fn_no_ext)
            shutil.copy(out.name, dest)
            err.close()
            update_fn(msg.uuid, self.session)


class MessageSync(APISyncObject):
    """
    Runs in the background, finding messages to download and downloading them.
    """

    def __init__(self, api, home, is_qubes):
        super().__init__(api, home, is_qubes)

    def run(self, loop=True):
        while True:
            submissions = storage.find_new_submissions(self.session)

            for db_submission in submissions:
                try:

                    # the API wants API objects. here in the client,
                    # we have client objects. let's take care of that
                    # here
                    sdk_submission = sdkobjects.Submission(
                        uuid=db_submission.uuid
                    )
                    sdk_submission.source_uuid = db_submission.source.uuid
                    # Need to set filename on non-Qubes platforms
                    sdk_submission.filename = db_submission.filename

                    self.fetch_the_thing(sdk_submission,
                                         db_submission,
                                         self.api.download_submission,
                                         storage.mark_file_as_downloaded)

                except Exception as e:
                    logger.critical(
                        "Exception while downloading submission! {}".format(e)
                    )

            if not loop:
                break
            else:
                time.sleep(5)  # pragma: no cover


class ReplySync(APISyncObject):
    """
    Runs in the background, finding replies to download and downloading them.
    """

    def __init__(self, api, home, is_qubes):
        super().__init__(api, home, is_qubes)

    def run(self, loop=True):
        while True:
            replies = storage.find_new_replies(self.session)

            for db_reply in replies:
                try:

                    # the API wants API objects. here in the client,
                    # we have client objects. let's take care of that
                    # here
                    sdk_reply = sdkobjects.Reply(
                        uuid=db_reply.uuid
                    )
                    sdk_reply.source_uuid = db_reply.source.uuid
                    # Need to set filename on non-Qubes platforms
                    sdk_reply.filename = db_reply.filename

                    self.fetch_the_thing(sdk_reply,
                                         db_reply,
                                         self.api.download_reply,
                                         storage.mark_reply_as_downloaded)

                except Exception as e:
                    logger.critical(
                        "Exception while downloading reply! {}".format(e)
                    )

            if not loop:
                break
            else:
                time.sleep(5)  # pragma: no cover
