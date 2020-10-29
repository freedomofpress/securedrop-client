"""Create models with a set of default valid properties, to avoid
changes forcing an update of all test code.
"""
import os
import uuid
from datetime import datetime
from itertools import cycle
from typing import List

from sdclientapi import Reply as SDKReply
from sdclientapi import Source as SDKSource

from securedrop_client import db
from securedrop_client.api_jobs.base import ApiJob

SOURCE_COUNT = 0
MESSAGE_COUNT = 0
FILE_COUNT = 0
REPLY_COUNT = 0
DRAFT_REPLY_COUNT = 0
REPLY_SEND_STATUS_COUNT = 0
USER_COUNT = 0


def User(**attrs):
    global USER_COUNT
    USER_COUNT += 1
    defaults = dict(
        uuid="user-uuid-{}".format(USER_COUNT),
        username="test-user-id-{}".format(USER_COUNT),
        firstname="slim",
        lastname="shady",
    )

    defaults.update(attrs)

    return db.User(**defaults)


def Source(**attrs):

    with open(os.path.join(os.path.dirname(__file__), "files", "test-key.gpg.pub.asc")) as f:
        pub_key = f.read()

    global SOURCE_COUNT
    SOURCE_COUNT += 1
    defaults = dict(
        uuid="source-uuid-{}".format(SOURCE_COUNT),
        journalist_designation="testy-mctestface",
        is_flagged=False,
        public_key=pub_key,
        fingerprint="B2FF7FB28EED8CABEBC5FB6C6179D97BCFA52E5F",
        interaction_count=0,
        is_starred=False,
        last_updated=datetime.now(),
        document_count=0,
    )

    defaults.update(attrs)

    return db.Source(**defaults)


def Message(**attrs):
    global MESSAGE_COUNT
    MESSAGE_COUNT += 1
    defaults = dict(
        uuid="msg-uuid-{}".format(MESSAGE_COUNT),
        filename="{}-msg.gpg".format(MESSAGE_COUNT),
        size=123,
        download_url="http://wat.onion/abc",
        is_decrypted=True,
        is_downloaded=True,
        content="content",
    )

    defaults.update(attrs)

    return db.Message(**defaults)


def Reply(**attrs):
    global REPLY_COUNT
    REPLY_COUNT += 1
    defaults = dict(
        uuid="reply-uuid-{}".format(REPLY_COUNT),
        filename="{}-reply.gpg".format(REPLY_COUNT),
        size=123,
        is_decrypted=True,
        is_downloaded=True,
        content="content",
    )

    defaults.update(attrs)

    return db.Reply(**defaults)


def DraftReply(**attrs):
    global DRAFT_REPLY_COUNT
    DRAFT_REPLY_COUNT += 1
    defaults = dict(
        timestamp=datetime.utcnow(),
        source_id=1,
        journalist_id=1,
        file_counter=1,
        uuid="draft-reply-uuid-{}".format(REPLY_COUNT),
        content="content",
        send_status_id=1,
    )

    defaults.update(attrs)

    return db.DraftReply(**defaults)


def ReplySendStatus(**attrs):
    global REPLY_SEND_STATUS_COUNT
    REPLY_SEND_STATUS_COUNT += 1
    defaults = dict(name=db.ReplySendStatusCodes.PENDING.value)

    defaults.update(attrs)

    return db.ReplySendStatus(**defaults)


def File(**attrs):
    global FILE_COUNT
    FILE_COUNT += 1
    defaults = dict(
        uuid="file-uuid-{}".format(FILE_COUNT),
        filename="{}-doc.gz.gpg".format(FILE_COUNT),
        size=123,
        download_url="http://wat.onion/abc",
        is_decrypted=True,
        is_downloaded=True,
    )

    defaults.update(attrs)

    return db.File(**defaults)


def dummy_job_factory(mocker, return_value, **kwargs):
    """
    Factory that creates dummy `ApiJob`s to DRY up test code.
    """

    class DummyApiJob(ApiJob):
        success_signal = mocker.MagicMock()
        failure_signal = mocker.MagicMock()

        def __init__(self, *nargs, **kwargs):
            super().__init__(*nargs, **kwargs)
            if isinstance(return_value, List):
                self.return_value = iter(return_value)
            else:
                self.return_value = cycle([return_value])

        def call_api(self, api_client, session):
            return_value = next(self.return_value)
            if isinstance(return_value, Exception):
                raise return_value
            else:
                return return_value

    return DummyApiJob


def RemoteSource(**attrs):

    with open(os.path.join(os.path.dirname(__file__), "files", "test-key.gpg.pub.asc")) as f:
        pub_key = f.read()

    defaults = dict(
        add_star_url="foo",
        interaction_count=0,
        is_flagged=False,
        is_starred=True,
        journalist_designation="testy-mctestface",
        key={"public": pub_key, "fingerprint": "B2FF7FB28EED8CABEBC5FB6C6179D97BCFA52E5F"},
        last_updated=datetime.now().isoformat(),
        number_of_documents=0,
        number_of_messages=0,
        remove_star_url="baz",
        replies_url="qux",
        submissions_url="wibble",
        url="url",
        uuid=str(uuid.uuid4()),
        seen_by=None,
    )

    defaults.update(attrs)

    return SDKSource(**defaults)


def RemoteReply(**attrs):

    source_url = "/api/v1/sources/{}".format(str(uuid.uuid4()))
    defaults = dict(
        filename="1-reply.filename",
        journalist_uuid=str(uuid.uuid4()),
        journalist_username="test",
        file_counter=1,
        is_deleted_by_source=False,
        reply_url="test",
        size=1234,
        uuid=str(uuid.uuid4()),
        source_url=source_url,
    )

    defaults.update(attrs)

    return SDKReply(**defaults)
