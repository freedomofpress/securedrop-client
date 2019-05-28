'''
Testing for the ApiJobQueue and related classes.
'''
import os
import pytest
import sdclientapi

from . import factory
from queue import Queue
from sdclientapi import AuthError, RequestTimeoutError
from typing import Tuple

from securedrop_client import db
from securedrop_client.crypto import GpgHelper, CryptoError
from securedrop_client.queue import ApiInaccessibleError, ApiJob, RunnableQueue, \
    DownloadSubmissionJob, ApiJobQueue


def test_ApiInaccessibleError_init():
    # check default value
    err = ApiInaccessibleError()
    assert str(err).startswith('API is inaccessible')
    assert isinstance(err, Exception)

    # check custom
    msg = 'foo'
    err = ApiInaccessibleError(msg)
    assert str(err) == msg


def test_ApiJob_raises_NotImplemetedError():
    job = ApiJob()

    with pytest.raises(NotImplementedError):
        job.call_api(None, None)


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


def test_ApiJob_no_api(mocker):
    return_value = 'wat'
    api_job_cls = dummy_job_factory(mocker, return_value)
    api_job = api_job_cls()

    mock_session = mocker.MagicMock()

    with pytest.raises(ApiInaccessibleError):
        api_job._do_call_api(None, mock_session)

    assert not api_job.success_signal.emit.called
    assert not api_job.failure_signal.emit.called


def test_ApiJob_success(mocker):
    return_value = 'wat'
    api_job_cls = dummy_job_factory(mocker, return_value)
    api_job = api_job_cls()

    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    api_job._do_call_api(mock_api_client, mock_session)

    api_job.success_signal.emit.assert_called_once_with(return_value)
    assert not api_job.failure_signal.emit.called


def test_ApiJob_auth_error(mocker):
    return_value = AuthError('oh no')
    api_job_cls = dummy_job_factory(mocker, return_value)
    api_job = api_job_cls()

    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    with pytest.raises(ApiInaccessibleError):
        api_job._do_call_api(mock_api_client, mock_session)

    assert not api_job.success_signal.emit.called
    assert not api_job.failure_signal.emit.called


def test_ApiJob_timeout_error(mocker):
    return_value = RequestTimeoutError()
    api_job_cls = dummy_job_factory(mocker, return_value)
    api_job = api_job_cls()

    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    with pytest.raises(RequestTimeoutError):
        api_job._do_call_api(mock_api_client, mock_session)

    assert not api_job.success_signal.emit.called
    assert not api_job.failure_signal.emit.called


def test_ApiJob_other_error(mocker):
    return_value = Exception()
    api_job_cls = dummy_job_factory(mocker, return_value)
    api_job = api_job_cls()

    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    api_job._do_call_api(mock_api_client, mock_session)

    assert not api_job.success_signal.emit.called
    api_job.failure_signal.emit.assert_called_once_with(return_value)


def test_RunnableQueue_init(mocker):
    mock_api_client = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock()

    queue = RunnableQueue(mock_api_client, mock_session_maker)
    assert queue.api_client == mock_api_client
    assert queue.session_maker == mock_session_maker
    assert isinstance(queue.queue, Queue)
    assert queue.queue.empty()
    assert queue.last_job is None


def test_RunnableQueue_happy_path(mocker):
    '''
    Add one job to the queue, run it.
    '''
    mock_process_events = mocker.patch('securedrop_client.queue.QApplication.processEvents')
    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock(return_value=mock_session)
    return_value = 'foo'

    dummy_job_cls = dummy_job_factory(mocker, return_value)

    queue = RunnableQueue(mock_api_client, mock_session_maker)
    queue.queue.put_nowait(dummy_job_cls())

    queue._process(exit_loop=True)

    # this needs to be called at the end of the loop
    assert mock_process_events.called

    assert queue.last_job is None
    assert queue.queue.empty()


def test_RunnableQueue_job_timeout(mocker):
    '''
    Add two jobs to the queue. The first times out, and then gets "cached" for the next pass
    through the loop.
    '''
    mock_process_events = mocker.patch('securedrop_client.queue.QApplication.processEvents')
    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock(return_value=mock_session)

    return_value = RequestTimeoutError()
    dummy_job_cls = dummy_job_factory(mocker, return_value)
    job1 = dummy_job_cls()
    job2 = dummy_job_cls()

    queue = RunnableQueue(mock_api_client, mock_session_maker)
    queue.queue.put_nowait(job1)
    queue.queue.put_nowait(job2)

    # attempt to process job1 knowing that it times out
    queue._process(exit_loop=True)

    # check that job1 is "cached" and a job is in the queue
    assert queue.last_job is job1
    assert queue.queue.qsize() == 1

    # update job1 to not raise an error so it can be processed
    job1.return_value = 'foo'

    # attempt to process the job1 again
    queue._process(exit_loop=True)

    # check that job has not been cached again
    assert queue.last_job is None
    assert queue.queue.qsize() == 1

    # attempt to process job2 knowing that it times out
    queue._process(exit_loop=True)

    # check that job2 was cached and that the queue is empty
    assert queue.last_job is job2
    assert queue.queue.empty()

    # ensure we don't have stale mocks
    assert mock_process_events.called


def test_DownloadSubmissionJob_happy_path_no_etag(mocker, homedir, session, session_maker):
    source = factory.Source()
    file_ = factory.File(source=source)
    session.add(source)
    session.add(file_)
    session.commit()

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    mock_decrypt = mocker.patch.object(gpg, 'decrypt_submission_or_reply')

    def fake_download(sdk_obj: sdclientapi.Submission) -> Tuple[str, str]:
        '''
        :return: (etag, path_to_dl)
        '''
        full_path = os.path.join(homedir, 'somepath')
        with open(full_path, 'wb') as f:
            f.write(b'')
        return ('', full_path)

    api_client = mocker.MagicMock()
    api_client.download_submission = fake_download

    job = DownloadSubmissionJob(
        db.File,
        file_.uuid,
        homedir,
        gpg,
    )

    mock_logger = mocker.patch('securedrop_client.queue.logger')

    job.call_api(api_client, session)

    log_msg = mock_logger.debug.call_args_list[0][0][0]
    assert log_msg.startswith('No ETag. Skipping integrity check')

    # ensure mocks aren't stale
    assert mock_decrypt.called


def test_DownloadSubmissionJob_happy_path_sha256_etag(mocker, homedir, session, session_maker):
    source = factory.Source()
    file_ = factory.File(source=source)
    session.add(source)
    session.add(file_)
    session.commit()

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    mock_decrypt = mocker.patch.object(gpg, 'decrypt_submission_or_reply')

    def fake_download(sdk_obj: sdclientapi.Submission) -> Tuple[str, str]:
        '''
        :return: (etag, path_to_dl)
        '''
        full_path = os.path.join(homedir, 'somepath')
        with open(full_path, 'wb') as f:
            f.write(b'wat')

        # sha256 of b'wat'
        return ('sha256:f00a787f7492a95e165b470702f4fe9373583fbdc025b2c8bdf0262cc48fcff4',
                full_path)

    api_client = mocker.MagicMock()
    api_client.download_submission = fake_download

    job = DownloadSubmissionJob(
        db.File,
        file_.uuid,
        homedir,
        gpg,
    )

    job.call_api(api_client, session)

    # ensure mocks aren't stale
    assert mock_decrypt.called


def test_DownloadSubmissionJob_bad_sha256_etag(mocker, homedir, session, session_maker):
    source = factory.Source()
    file_ = factory.File(source=source)
    session.add(source)
    session.add(file_)
    session.commit()

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)

    def fake_download(sdk_obj: sdclientapi.Submission) -> Tuple[str, str]:
        '''
        :return: (etag, path_to_dl)
        '''
        full_path = os.path.join(homedir, 'somepath')
        with open(full_path, 'wb') as f:
            f.write(b'')

        return ('sha256:not-a-sha-sum',
                full_path)

    api_client = mocker.MagicMock()
    api_client.download_submission = fake_download

    job = DownloadSubmissionJob(
        db.File,
        file_.uuid,
        homedir,
        gpg,
    )

    # we currently don't handle errors in the checksum
    with pytest.raises(RuntimeError):
        job.call_api(api_client, session)


def test_DownloadSubmissionJob_happy_path_unknown_etag(mocker, homedir, session, session_maker):
    source = factory.Source()
    file_ = factory.File(source=source)
    session.add(source)
    session.add(file_)
    session.commit()

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)

    def fake_download(sdk_obj: sdclientapi.Submission) -> Tuple[str, str]:
        '''
        :return: (etag, path_to_dl)
        '''
        full_path = os.path.join(homedir, 'somepath')
        with open(full_path, 'wb') as f:
            f.write(b'')
        return ('UNKNOWN:abc123',
                full_path)

    api_client = mocker.MagicMock()
    api_client.download_submission = fake_download

    job = DownloadSubmissionJob(
        db.File,
        file_.uuid,
        homedir,
        gpg,
    )

    mock_decrypt = mocker.patch('securedrop_client.crypto.GpgHelper.decrypt_submission_or_reply')
    mock_logger = mocker.patch('securedrop_client.queue.logger')

    job.call_api(api_client, session)

    log_msg = mock_logger.debug.call_args_list[0][0][0]
    assert log_msg.startswith('Unknown hash algorithm')

    # ensure mocks aren't stale
    assert mock_decrypt.called


def test_DownloadSubmissionJob_decryption_error(mocker, homedir, session, session_maker):
    source = factory.Source()
    file_ = factory.File(source=source)
    session.add(source)
    session.add(file_)
    session.commit()

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    mock_decrypt = mocker.patch.object(gpg, 'decrypt_submission_or_reply',
                                       side_effect=CryptoError)

    def fake_download(sdk_obj: sdclientapi.Submission) -> Tuple[str, str]:
        '''
        :return: (etag, path_to_dl)
        '''
        full_path = os.path.join(homedir, 'somepath')
        with open(full_path, 'wb') as f:
            f.write(b'wat')

        # sha256 of b'wat'
        return ('sha256:f00a787f7492a95e165b470702f4fe9373583fbdc025b2c8bdf0262cc48fcff4',
                full_path)

    api_client = mocker.MagicMock()
    api_client.download_submission = fake_download

    job = DownloadSubmissionJob(
        db.File,
        file_.uuid,
        homedir,
        gpg,
    )

    mock_logger = mocker.patch('securedrop_client.queue.logger')

    with pytest.raises(CryptoError):
        job.call_api(api_client, session)

    log_msg = mock_logger.debug.call_args_list[0][0][0]
    assert log_msg.startswith('Failed to decrypt file')

    # ensure mocks aren't stale
    assert mock_decrypt.called


def test_ApiJobQueue_enqueue(mocker):
    mock_client = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock()

    job_queue = ApiJobQueue(mock_client, mock_session_maker)
    mock_download_queue = mocker.patch.object(job_queue, 'download_queue')
    mock_main_queue = mocker.patch.object(job_queue, 'main_queue')

    dl_job = DownloadSubmissionJob(db.File, 'mock', 'mock', 'mock')
    job_queue.enqueue(dl_job)

    mock_download_queue.queue.put_nowait.assert_called_once_with(dl_job)
    assert not mock_main_queue.queue.put_nowait.called

    # reset for next test
    mock_download_queue.reset_mock()
    mock_main_queue.reset_mock()

    dummy_job = dummy_job_factory(mocker, 'mock')()
    job_queue.enqueue(dummy_job)

    mock_main_queue.queue.put_nowait.assert_called_once_with(dummy_job)
    assert not mock_download_queue.queue.put_nowait.called


def test_ApiJobQueue_start_queues(mocker):
    mock_api = mocker.MagicMock()
    mock_client = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock()

    job_queue = ApiJobQueue(mock_client, mock_session_maker)

    mock_main_queue = mocker.patch.object(job_queue, 'main_queue')
    mock_download_queue = mocker.patch.object(job_queue, 'download_queue')
    mock_main_thread = mocker.patch.object(job_queue, 'main_thread')
    mock_download_thread = mocker.patch.object(job_queue, 'download_thread')

    job_queue.start_queues(mock_api)

    assert mock_main_queue.api_client == mock_api
    assert mock_download_queue.api_client == mock_api

    mock_main_thread.start.assert_called_once_with()
    mock_download_thread.start.assert_called_once_with()
