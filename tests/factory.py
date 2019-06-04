"""Create models with a set of default valid properties, to avoid
changes forcing an update of all test code.
"""
from datetime import datetime
from securedrop_client import db
from securedrop_client.api_jobs.base import ApiJob

SOURCE_COUNT = 0
MESSAGE_COUNT = 0
FILE_COUNT = 0
REPLY_COUNT = 0
USER_COUNT = 0


def User(**attrs):
    global USER_COUNT
    USER_COUNT += 1
    defaults = dict(
        uuid='user-uuid-{}'.format(USER_COUNT),
        username='test-user-id-{}'.format(USER_COUNT),
    )

    defaults.update(attrs)

    return db.User(**defaults)


def Source(**attrs):
    global SOURCE_COUNT
    SOURCE_COUNT += 1
    defaults = dict(
        uuid='source-uuid-{}'.format(SOURCE_COUNT),
        journalist_designation='testy-mctestface',
        is_flagged=False,
        public_key='mah pub key',
        interaction_count=0,
        is_starred=False,
        last_updated=datetime.now(),
        document_count=0
    )

    defaults.update(attrs)

    return db.Source(**defaults)


def Message(**attrs):
    global MESSAGE_COUNT
    MESSAGE_COUNT += 1
    defaults = dict(
        uuid='source-uuid-{}'.format(MESSAGE_COUNT),
        filename='{}-msg.gpg'.format(MESSAGE_COUNT),
        size=123,
        download_url='http://wat.onion/abc',
        is_decrypted=True,
        is_downloaded=True,
        content='content',
    )

    defaults.update(attrs)

    return db.Message(**defaults)


def Reply(**attrs):
    global REPLY_COUNT
    REPLY_COUNT += 1
    defaults = dict(
        uuid='source-uuid-{}'.format(REPLY_COUNT),
        filename='{}-reply.gpg'.format(REPLY_COUNT),
        size=123,
        is_decrypted=True,
        is_downloaded=True,
        content='content',
    )

    defaults.update(attrs)

    return db.Reply(**defaults)


def File(**attrs):
    global FILE_COUNT
    FILE_COUNT += 1
    defaults = dict(
        uuid='source-uuid-{}'.format(FILE_COUNT),
        filename='{}-doc.gz.gpg'.format(FILE_COUNT),
        size=123,
        download_url='http://wat.onion/abc',
        is_decrypted=True,
        is_downloaded=True,
    )

    defaults.update(attrs)

    return db.File(**defaults)


def dummy_job_factory(mocker, return_value):
    '''
    Factory that creates dummy `ApiJob`s to DRY up test code.
    '''
    class DummyApiJob(ApiJob):
        success_signal = mocker.MagicMock()
        failure_signal = mocker.MagicMock()

        def __init__(self, *nargs, **kwargs):
            super().__init__(*nargs, **kwargs)
            self.return_value = return_value

        def call_api(self, api_client, session):
            if isinstance(self.return_value, Exception):
                raise self.return_value
            else:
                return self.return_value

    return DummyApiJob
