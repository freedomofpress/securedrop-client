'''
Testing for the ApiJobQueue and related classes.
'''
from queue import Queue
from sdclientapi import RequestTimeoutError

from securedrop_client.api_jobs.downloads import FileDownloadJob
from securedrop_client.api_jobs.base import ApiInaccessibleError
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


def test_RunnableQueue_happy_path(mocker):
    '''
    Add one job to the queue, run it.
    '''
    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock(return_value=mock_session)
    return_value = 'foo'

    dummy_job_cls = factory.dummy_job_factory(mocker, return_value)

    queue = RunnableQueue(mock_api_client, mock_session_maker)
    job_priority = 1
    queue.add_job(job_priority, dummy_job_cls())

    queue._process(exit_loop=True)

    assert queue.queue.empty()


def test_RunnableQueue_job_timeout(mocker):
    '''
    Add two jobs to the queue. The first times out, and then gets resubmitted for the next pass
    through the loop.
    '''
    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock(return_value=mock_session)

    return_value = RequestTimeoutError()
    times_to_try = 5
    dummy_job_cls = factory.dummy_job_factory(mocker, return_value,
                                              remaining_attempts=times_to_try)
    job1 = dummy_job_cls()
    job2 = dummy_job_cls()

    queue = RunnableQueue(mock_api_client, mock_session_maker)
    job_priority = 1
    queue.add_job(job_priority, job1)
    queue.add_job(job_priority, job2)

    # attempt to process job1 knowing that it times out
    queue._process(exit_loop=True)

    # there should be two jobs in the queue
    assert queue.queue.qsize() == 2

    # update job1 to not raise an error so it can be processed
    job1.return_value = 'foo'

    # attempt to process the job1 again
    queue._process(exit_loop=True)

    # now there should just be one job: job1 was processed successfully
    assert queue.queue.qsize() == 1

    # attempt to process job2 knowing that it times out
    queue._process(exit_loop=True)

    # check that job2 was resubmitted
    assert queue.queue.qsize() == 1

    # check that job2 still has 5 (the default) remaining attempts
    assert job2.remaining_attempts == times_to_try


def test_RunnableQueue_job_ApiInaccessibleError(mocker):
    '''
    Add two jobs to the queue, the first of which will cause an ApiInaccessibleError.
    Ensure that the queue continues processing jobs and the second job is attempted.
    (this is behavior until we have a signal that pauses job execution when
    ApiInaccessibleError occurs, see #379).
    '''

    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock(return_value=mock_session)

    return_value = ApiInaccessibleError()
    dummy_job_cls = factory.dummy_job_factory(mocker, return_value)
    job_priority = 2

    job1 = dummy_job_cls()
    job2 = dummy_job_cls()

    queue = RunnableQueue(mock_api_client, mock_session_maker)
    queue.add_job(job_priority, job1)
    queue.add_job(job_priority, job2)

    # attempt to process job1 knowing that we'll have an auth error, which should be handled.
    queue._process(exit_loop=True)

    # check that one more job is in the queue
    assert queue.queue.qsize() == 1

    # update job2 to not raise an error so it can be processed
    job2.return_value = 'job will process this!'

    # run next job in the queue to process job2
    queue._process(exit_loop=True)

    # check that all jobs are gone
    assert queue.queue.empty()


def test_RunnableQueue_job_generic_exception(mocker):
    '''
    Add two jobs to the queue, the first of which will cause a generic exception.
    Ensure that the queue continues processing jobs and the second job is attempted.
    '''

    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock(return_value=mock_session)

    return_value = Exception()
    dummy_job_cls = factory.dummy_job_factory(mocker, return_value)
    job1 = dummy_job_cls()
    job2 = dummy_job_cls()

    queue = RunnableQueue(mock_api_client, mock_session_maker)
    job_priority = 2
    queue.add_job(job_priority, job1)
    queue.add_job(job_priority, job2)

    # Attempt to process job1 knowing that we'll have a generic exception, which should be handled.
    # Note: generic exceptions get handled in _do_call_api in case you're wondering why this doesn't
    # raise an exception.
    queue._process(exit_loop=True)

    # check that one more job is in the queue
    assert queue.queue.qsize() == 1

    # update job2 to not raise an error so it can be processed
    job2.return_value = 'job will process this!'

    # run next job in the queue to process job2
    queue._process(exit_loop=True)

    # check that all jobs are gone
    assert queue.queue.empty()


def test_RunnableQueue_does_not_run_jobs_when_not_authed(mocker):
    '''
    Add a job to the queue, ensure we don't run it when not authenticated.
    '''
    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock(return_value=mock_session)

    return_value = ApiInaccessibleError()
    dummy_job_cls = factory.dummy_job_factory(mocker, return_value)
    job = dummy_job_cls()
    job_priority = 2

    queue = RunnableQueue(mock_api_client, mock_session_maker)
    queue.add_job(job_priority, job)

    mock_logger = mocker.patch('securedrop_client.queue.logger')

    # attempt to process job
    queue._process(exit_loop=True)

    # assert we logged an error message
    assert "Client is not authenticated" in mock_logger.error.call_args[0][0]


def test_ApiJobQueue_enqueue(mocker):
    mock_client = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock()

    job_queue = ApiJobQueue(mock_client, mock_session_maker)
    job_priority = 2
    dummy_job = factory.dummy_job_factory(mocker, 'mock')()
    job_queue.JOB_PRIORITIES = {FileDownloadJob: job_priority, type(dummy_job): job_priority}

    mock_download_file_queue = mocker.patch.object(job_queue, 'download_file_queue')
    mock_main_queue = mocker.patch.object(job_queue, 'main_queue')
    mock_download_file_add_job = mocker.patch.object(mock_download_file_queue, 'add_job')
    mock_main_queue_add_job = mocker.patch.object(mock_main_queue, 'add_job')
    job_queue.main_queue.api_client = 'has a value'
    job_queue.download_file_queue.api_client = 'has a value'
    mock_start_queues = mocker.patch.object(job_queue, 'start_queues')

    dl_job = FileDownloadJob('mock', 'mock', 'mock')
    job_queue.enqueue(dl_job)

    mock_download_file_add_job.assert_called_once_with(job_priority, dl_job)
    assert not mock_main_queue_add_job.called

    # reset for next test
    mock_download_file_queue.reset_mock()
    mock_download_file_add_job.reset_mock()
    mock_main_queue.reset_mock()
    mock_main_queue_add_job.reset_mock()

    job_queue.enqueue(dummy_job)

    mock_main_queue_add_job.assert_called_once_with(job_priority, dummy_job)
    assert not mock_download_file_add_job.called
    assert mock_start_queues.called


def test_ApiJobQueue_enqueue_no_auth(mocker):
    mock_client = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock()

    job_queue = ApiJobQueue(mock_client, mock_session_maker)
    mock_download_file_queue = mocker.patch.object(job_queue, 'download_file_queue')
    mock_main_queue = mocker.patch.object(job_queue, 'main_queue')
    mock_download_file_add_job = mocker.patch.object(mock_download_file_queue, 'add_job')
    mock_main_queue_add_job = mocker.patch.object(mock_main_queue, 'add_job')
    job_queue.main_queue.api_client = None
    job_queue.download_file_queue.api_client = None
    mock_start_queues = mocker.patch.object(job_queue, 'start_queues')

    dummy_job = factory.dummy_job_factory(mocker, 'mock')()
    job_queue.enqueue(dummy_job)

    assert not mock_download_file_add_job.called
    assert not mock_main_queue_add_job.called
    assert not mock_start_queues.called


def test_ApiJobQueue_login_if_queues_not_running(mocker):
    mock_api = mocker.MagicMock()
    mock_client = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock()

    job_queue = ApiJobQueue(mock_client, mock_session_maker)

    mock_main_queue = mocker.patch.object(job_queue, 'main_queue')
    mock_download_file_queue = mocker.patch.object(job_queue, 'download_file_queue')
    mock_main_thread = mocker.patch.object(job_queue, 'main_thread')
    mock_download_file_thread = mocker.patch.object(job_queue, 'download_file_thread')
    job_queue.main_thread.isRunning = mocker.MagicMock(return_value=False)
    job_queue.download_file_thread.isRunning = mocker.MagicMock(return_value=False)

    job_queue.login(mock_api)

    assert mock_main_queue.api_client == mock_api
    assert mock_download_file_queue.api_client == mock_api

    mock_main_thread.start.assert_called_once_with()
    mock_download_file_thread.start.assert_called_once_with()


def test_ApiJobQueue_login_if_queues_running(mocker):
    mock_api = mocker.MagicMock()
    mock_client = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock()

    job_queue = ApiJobQueue(mock_client, mock_session_maker)

    mock_main_queue = mocker.patch.object(job_queue, 'main_queue')
    mock_download_file_queue = mocker.patch.object(job_queue, 'download_file_queue')
    mock_main_thread = mocker.patch.object(job_queue, 'main_thread')
    mock_download_file_thread = mocker.patch.object(job_queue, 'download_file_thread')
    job_queue.main_thread.isRunning = mocker.MagicMock(return_value=True)
    job_queue.download_file_thread.isRunning = mocker.MagicMock(return_value=True)

    job_queue.login(mock_api)

    assert mock_main_queue.api_client == mock_api
    assert mock_download_file_queue.api_client == mock_api

    assert not mock_main_thread.start.called
    assert not mock_download_file_thread.start.called


def test_ApiJobQueue_logout_removes_api_client(mocker):
    mock_client = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock()

    job_queue = ApiJobQueue(mock_client, mock_session_maker)
    job_queue.main_queue.api_client = 'my token!!!'
    job_queue.download_file_queue.api_client = 'my token!!!'

    job_queue.logout()

    assert job_queue.main_queue.api_client is None
    assert job_queue.download_file_queue.api_client is None
