'''
Testing for the ApiJobQueue and related classes.
'''
from queue import Queue
from sdclientapi import RequestTimeoutError

from securedrop_client.api_jobs.downloads import FileDownloadJob
from securedrop_client.queue import RunnableQueue, ApiJobQueue
from tests import factory


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

    dummy_job_cls = factory.dummy_job_factory(mocker, return_value)

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
    dummy_job_cls = factory.dummy_job_factory(mocker, return_value)
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


def test_ApiJobQueue_enqueue(mocker):
    mock_client = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock()

    job_queue = ApiJobQueue(mock_client, mock_session_maker)
    mock_download_file_queue = mocker.patch.object(job_queue, 'download_file_queue')
    mock_main_queue = mocker.patch.object(job_queue, 'main_queue')

    dl_job = FileDownloadJob('mock', 'mock', 'mock')
    job_queue.enqueue(dl_job)

    mock_download_file_queue.queue.put_nowait.assert_called_once_with(dl_job)
    assert not mock_main_queue.queue.put_nowait.called

    # reset for next test
    mock_download_file_queue.reset_mock()
    mock_main_queue.reset_mock()

    dummy_job = factory.dummy_job_factory(mocker, 'mock')()
    job_queue.enqueue(dummy_job)

    mock_main_queue.queue.put_nowait.assert_called_once_with(dummy_job)
    assert not mock_download_file_queue.queue.put_nowait.called


def test_ApiJobQueue_start_queues(mocker):
    mock_api = mocker.MagicMock()
    mock_client = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock()

    job_queue = ApiJobQueue(mock_client, mock_session_maker)

    mock_main_queue = mocker.patch.object(job_queue, 'main_queue')
    mock_download_file_queue = mocker.patch.object(job_queue, 'download_file_queue')
    mock_main_thread = mocker.patch.object(job_queue, 'main_thread')
    mock_download_file_thread = mocker.patch.object(job_queue, 'download_file_thread')

    job_queue.start_queues(mock_api)

    assert mock_main_queue.api_client == mock_api
    assert mock_download_file_queue.api_client == mock_api

    mock_main_thread.start.assert_called_once_with()
    mock_download_file_thread.start.assert_called_once_with()
