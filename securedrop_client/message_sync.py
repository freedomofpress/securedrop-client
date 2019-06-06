"""
Contains the ReplySync class, which runs in the background and loads new
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
import traceback
import sdclientapi.sdlocalobjects as sdkobjects
from sdclientapi import API
from typing import Callable, Union

from PyQt5.QtCore import QObject, pyqtSignal
from securedrop_client import storage
from securedrop_client.crypto import GpgHelper, CryptoError
from securedrop_client.db import File, Message, Reply
from sqlalchemy.orm import scoped_session
from sqlalchemy.orm.session import Session
from tempfile import NamedTemporaryFile


logger = logging.getLogger(__name__)


class APISyncObject(QObject):

    def __init__(
        self,
        api: API,
        gpg: GpgHelper,
        session_maker: scoped_session,
    ) -> None:
        super().__init__()
        self.api = api
        self.gpg = gpg
        self.session_maker = session_maker

    def decrypt_the_thing(
        self,
        session: Session,
        filepath: str,
        msg: Union[File, Message, Reply],
    ) -> None:
        with NamedTemporaryFile('w+') as plaintext_file:
            try:
                self.gpg.decrypt_submission_or_reply(filepath, plaintext_file.name, False)
                plaintext_file.seek(0)
                content = plaintext_file.read()
                storage.set_object_decryption_status_with_content(msg, session, True, content)
                logger.info("Message or reply decrypted: {}".format(msg.filename))
            except CryptoError:
                storage.set_object_decryption_status_with_content(msg, session, False)
                logger.info("Message or reply failed to decrypt: {}".format(msg.filename))

    def fetch_the_thing(
        self,
        session: Session,
        item: Union[File, Message, Reply],
        msg: Union[File, Message, Reply],
        download_fn: Callable,
        update_fn: Callable,
    ) -> None:
        _, filepath = download_fn(item)
        update_fn(msg.uuid, session)
        logger.info("Stored message or reply at {}".format(msg.filename))
        self.decrypt_the_thing(session, filepath, msg)


class ReplySync(APISyncObject):
    """
    Runs in the background, finding replies to download and downloading them.
    """

    """
    Signal emitted notifying that a reply is ready to be displayed. The signal is a tuple of
    (str, str) containing the reply's UUID and the content of the reply.
    """
    reply_ready = pyqtSignal([str, str])

    def run(self, loop: bool = True) -> None:
        session = self.session_maker()
        while True:
            replies = storage.find_new_replies(session)

            for db_reply in replies:
                try:
                    # the API wants API objects. here in the client,
                    # we have client objects. let's take care of that
                    # here
                    sdk_reply = sdkobjects.Reply(
                        uuid=db_reply.uuid,
                        filename=db_reply.filename,
                    )
                    sdk_reply.source_uuid = db_reply.source.uuid
                    # Need to set filename on non-Qubes platforms

                    if not db_reply.is_downloaded and self.api:
                        # Download and decrypt
                        self.fetch_the_thing(session,
                                             sdk_reply,
                                             db_reply,
                                             self.api.download_reply,
                                             storage.mark_reply_as_downloaded)
                    elif db_reply.is_downloaded:
                        # Just decrypt file that is already on disk
                        self.decrypt_the_thing(session,
                                               db_reply.filename,
                                               db_reply)

                    if db_reply.content is not None:
                        content = db_reply.content
                    else:
                        content = '<Reply not yet available>'

                    self.reply_ready.emit(db_reply.uuid, content)
                except Exception:
                    tb = traceback.format_exc()
                    logger.critical("Exception while processing reply!\n{}".format(tb))

            logger.debug('Replies synced')

            if not loop:
                break
            else:
                time.sleep(5)  # pragma: no cover
