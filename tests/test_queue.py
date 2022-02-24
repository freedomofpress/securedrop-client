"""
Testing for the ApiJobQueue and related classes.
"""
from queue import Queue

import pytest
from sdclientapi import RequestTimeoutError, ServerConnectionError

from securedrop_client.api_jobs.base import ApiInaccessibleError, PauseQueueJob
from securedrop_client.api_jobs.downloads import FileDownloadJob, MessageDownloadJob
from securedrop_client.api_jobs.uploads import SendReplyJob
from securedrop_client.queue import ApiJobQueue, RunnableQueue
from tests import factory


def test_RunnableQueue_init(mocker):
    mock_api_client = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock()
    mocker.patch("securedrop_client.queue.RunnableQueue.resume", return_value=mocker.MagicMock())

    queue = RunnableQueue(mock_api_client, mock_session_maker)

    assert queue.api_client == mock_api_client
    assert queue.session_maker == mock_session_maker
    assert isinstance(queue.queue, Queue)
    assert queue.queue.empty()
    queue.resume.connect.assert_called_once_with(queue.process)


def test_RunnableQueue_happy_path(mocker):
    """
    Add one job to the queue, run it.
    """
    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock(return_value=mock_session)
    return_value = "foo"

    dummy_job_cls = factory.dummy_job_factory(mocker, return_value)
    queue = RunnableQueue(mock_api_client, mock_session_maker)
    queue.JOB_PRIORITIES = {dummy_job_cls: 1, PauseQueueJob: 2}

    queue.add_job(dummy_job_cls())
    queue.add_job(PauseQueueJob())  # Pause queue so our test exits the processing loop
    queue.process()

    assert queue.queue.empty()


@pytest.mark.parametrize("exception", [RequestTimeoutError, ServerConnectionError])
def test_RunnableQueue_job_timeout(mocker, exception):
    """
    Add two jobs to the queue. The first times out, and then gets resubmitted for the next pass
    through the loop.
    """
    queue = RunnableQueue(mocker.MagicMock(), mocker.MagicMock())
    queue.pause = mocker.MagicMock()
    job_cls = factory.dummy_job_factory(mocker, exception(), remaining_attempts=5)
    job1 = job_cls()
    job2 = job_cls()
    queue.JOB_PRIORITIES = {PauseQueueJob: 0, job_cls: 1}

    # RequestTimeoutError or ServerConnectionError will cause the queue to pause,
    # use our fake pause method instead
    def fake_pause() -> None:
        queue.add_job(PauseQueueJob())

    queue.pause.emit = fake_pause

    # Add two jobs that timeout during processing to the queue
    queue.add_job(job1)
    queue.add_job(job2)

    # attempt to process job1 knowing that it times out
    queue.process()
    assert queue.queue.qsize() == 2  # queue contains: job1, job2

    # now process after making it so job1 no longer times out
    job1.return_value = "mock"
    queue.process()
    assert queue.queue.qsize() == 1  # queue contains: job2
    assert queue.queue.get(block=True) == (1, job2)


def test_RunnableQueue_process_PauseQueueJob(mocker):
    api_client = mocker.MagicMock()
    session_maker = mocker.MagicMock(return_value=mocker.MagicMock())
    queue = RunnableQueue(api_client, session_maker)
    queue.JOB_PRIORITIES = {PauseQueueJob: 11}

    queue.add_job(PauseQueueJob())
    queue.process()

    assert queue.queue.empty()


def test_RunnableQueue_high_priority_jobs_run_first_and_in_fifo_order(mocker):
    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock(return_value=mock_session)

    return_value = "wat"

    job_cls_high_priority = factory.dummy_job_factory(mocker, return_value)
    job_cls_low_priority = factory.dummy_job_factory(mocker, return_value)
    queue = RunnableQueue(mock_api_client, mock_session_maker)
    queue.JOB_PRIORITIES = {job_cls_high_priority: 1, job_cls_low_priority: 2}

    job1 = job_cls_high_priority()
    job2 = job_cls_low_priority()
    job3 = job_cls_high_priority()
    job4 = job_cls_low_priority()

    queue.add_job(job1)
    queue.add_job(job2)
    queue.add_job(job3)
    queue.add_job(job4)

    # Expected order of execution is job1 -> job3 -> job2 -> job4
    assert queue.queue.get(block=True) == (1, job1)
    assert queue.queue.get(block=True) == (1, job3)
    assert queue.queue.get(block=True) == (2, job2)
    assert queue.queue.get(block=True) == (2, job4)


def test_RunnableQueue_resubmitted_jobs(mocker):
    """
    Verify that jobs that fail due to timeout are resubmitted without modifying order_number.
    """
    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock(return_value=mock_session)

    job_cls_high_priority = factory.dummy_job_factory(mocker, "mock")
    job_cls_low_priority = factory.dummy_job_factory(mocker, "mock")
    queue = RunnableQueue(mock_api_client, mock_session_maker)
    queue.JOB_PRIORITIES = {job_cls_high_priority: 1, job_cls_low_priority: 2}

    job1 = job_cls_high_priority()
    job2 = job_cls_low_priority()
    job3 = job_cls_high_priority()
    job4 = job_cls_low_priority()

    queue.add_job(job1)
    queue.add_job(job2)
    queue.add_job(job3)
    queue.add_job(job4)

    # Expected order of execution is job1 -> job3 -> job2 -> job4
    assert queue.queue.get(block=True) == (1, job1)

    # Now resubmit job1 via put_nowait. It should execute prior to job2-4.
    with queue.condition_add_or_remove_job:
        queue._re_add_job(job1)
    assert queue.queue.get(block=True) == (1, job1)
    assert queue.queue.get(block=True) == (1, job3)
    assert queue.queue.get(block=True) == (2, job2)
    assert queue.queue.get(block=True) == (2, job4)


def test_RunnableQueue_duplicate_jobs(mocker):
    """
    Verify that duplicate jobs are not added to the queue.
    """
    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock(return_value=mock_session)

    dl_job = FileDownloadJob("mock", "mock", "mock")
    msg_dl_job = MessageDownloadJob("mock", "mock", "mock")
    queue = RunnableQueue(mock_api_client, mock_session_maker)
    debug_logger = mocker.patch("securedrop_client.queue.logger.debug")

    # Queue begins empty (0 entries).
    assert len(queue.queue.queue) == 0

    queue.add_job(dl_job)
    assert len(queue.queue.queue) == 1

    # Now add the same job again.
    queue.add_job(dl_job)
    assert len(queue.queue.queue) == 1

    log_msg = "Duplicate job {}, skipping".format(dl_job)
    debug_logger.call_args[1] == log_msg

    # Now add a _different_ job with the same arguments (same uuid).
    queue.add_job(msg_dl_job)
    assert len(queue.queue.queue) == 2

    # Ensure that using _re_add_job in the case of a timeout won't allow duplicate
    # jobs to be added.
    with queue.condition_add_or_remove_job:
        queue._re_add_job(msg_dl_job)
    assert len(queue.queue.queue) == 2


def test_RunnableQueue_job_generic_exception(mocker):
    """
    Add two jobs to the queue, the first of which will cause a generic exception, which is handled
    in _do_call_api. Ensure that the queue continues processing jobs after dropping a job that
    runs into a generic exception.
    """
    job1_cls = factory.dummy_job_factory(mocker, Exception())  # processing skips job
    job2_cls = factory.dummy_job_factory(mocker, "mock")
    job1 = job1_cls()
    job2 = job2_cls()
    queue = RunnableQueue(mocker.MagicMock(), mocker.MagicMock())
    queue.JOB_PRIORITIES = {PauseQueueJob: 3, job1_cls: 2, job2_cls: 2}

    queue.add_job(job1)
    queue.add_job(job2)
    queue.add_job(PauseQueueJob())  # Pause queue so our test exits the processing loop

    queue.process()

    # check that all jobs are gone
    assert queue.queue.empty()


def test_RunnableQueue_does_not_run_jobs_when_not_authed(mocker):
    """
    Check that a job that sees an ApiInaccessibleError does not get resubmitted since it is not
    authorized and that its api_client is None.
    """
    queue = RunnableQueue(mocker.MagicMock(), mocker.MagicMock())
    job_cls = factory.dummy_job_factory(mocker, ApiInaccessibleError())
    queue.JOB_PRIORITIES = {PauseQueueJob: 0, job_cls: 1}

    # Add a job that results in an ApiInaccessibleError to the queue
    job = job_cls()
    queue.add_job(job)

    # attempt to process job knowing that it errors
    queue.process()
    assert queue.queue.qsize() == 0  # queue should not contain job since it was not resubmitted
    assert queue.api_client is None


def test_RunnableQueue_clear(mocker):
    """
    After RunnableQueue.clear(), the underlying PriorityQueue is empty.
    """
    api_client = mocker.MagicMock()
    session_maker = mocker.MagicMock(return_value=mocker.MagicMock())
    queue = RunnableQueue(api_client, session_maker)

    job = SendReplyJob("mock", "mock", "mock", "mock")
    queue.add_job(job)
    assert queue.queue.qsize() == 1

    queue.clear()
    assert queue.queue.empty()


def test_ApiJobQueue_enqueue_when_queues_are_running(mocker):
    mock_client = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock()

    job_queue = ApiJobQueue(mock_client, mock_session_maker)
    job_priority = 2
    dummy_job = factory.dummy_job_factory(mocker, "mock")()
    job_queue.JOB_PRIORITIES = {FileDownloadJob: job_priority, type(dummy_job): job_priority}

    mock_download_file_queue = mocker.patch.object(job_queue, "download_file_queue")
    mock_main_queue = mocker.patch.object(job_queue, "main_queue")
    mock_download_file_add_job = mocker.patch.object(mock_download_file_queue, "add_job")
    mock_main_queue_add_job = mocker.patch.object(mock_main_queue, "add_job")
    job_queue.main_queue.api_client = "has a value"
    job_queue.download_file_queue.api_client = "has a value"

    job_queue.main_thread.isRunning = mocker.MagicMock(return_value=True)
    job_queue.download_file_thread.isRunning = mocker.MagicMock(return_value=True)

    dl_job = FileDownloadJob("mock", "mock", "mock")
    job_queue.enqueue(dl_job)

    mock_download_file_add_job.assert_called_once_with(dl_job)
    assert not mock_main_queue_add_job.called

    # reset for next test
    mock_download_file_queue.reset_mock()
    mock_download_file_add_job.reset_mock()
    mock_main_queue.reset_mock()
    mock_main_queue_add_job.reset_mock()

    job_queue.enqueue(FileDownloadJob("mock", "mock", "mock"))

    assert not mock_main_queue_add_job.called

    # reset for next test
    mock_download_file_queue.reset_mock()
    mock_download_file_add_job.reset_mock()
    mock_main_queue.reset_mock()
    mock_main_queue_add_job.reset_mock()

    job_queue.enqueue(dummy_job)

    mock_main_queue_add_job.assert_called_once_with(dummy_job)
    assert not mock_download_file_add_job.called


def test_ApiJobQueue_enqueue_when_queues_are_not_running(mocker):
    mock_client = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock()

    job_queue = ApiJobQueue(mock_client, mock_session_maker)
    job_priority = 2
    dummy_job = factory.dummy_job_factory(mocker, "mock")()
    job_queue.JOB_PRIORITIES = {FileDownloadJob: job_priority, type(dummy_job): job_priority}

    mock_download_file_queue = mocker.patch.object(job_queue, "download_file_queue")
    mock_main_queue = mocker.patch.object(job_queue, "main_queue")
    mock_download_file_add_job = mocker.patch.object(mock_download_file_queue, "add_job")
    mock_main_queue_add_job = mocker.patch.object(mock_main_queue, "add_job")
    job_queue.main_queue.api_client = "has a value"
    job_queue.download_file_queue.api_client = "has a value"

    job_queue.stop()  # queues are already not running, but just in case the code changes one day

    dl_job = FileDownloadJob("mock", "mock", "mock")
    job_queue.enqueue(dl_job)

    mock_download_file_add_job.assert_not_called()
    mock_main_queue_add_job.assert_not_called()


def test_ApiJobQueue_on_main_queue_paused(mocker):
    job_queue = ApiJobQueue(mocker.MagicMock(), mocker.MagicMock())
    mocker.patch.object(job_queue, "paused")
    pause_job = PauseQueueJob()
    mocker.patch("securedrop_client.queue.PauseQueueJob", return_value=pause_job)

    job_queue.on_main_queue_paused()

    job_queue.paused.emit.assert_called_once_with()


def test_ApiJobQueue_on_file_download_queue_paused(mocker):
    job_queue = ApiJobQueue(mocker.MagicMock(), mocker.MagicMock())
    mocker.patch.object(job_queue, "paused")
    pause_job = PauseQueueJob()
    mocker.patch("securedrop_client.queue.PauseQueueJob", return_value=pause_job)

    job_queue.on_file_download_queue_paused()

    job_queue.paused.emit.assert_called_once_with()


def test_ApiJobQueue_resume_queues_emits_resume_signal_if_queues_are_running(mocker):
    """
    Ensure resume signal is emitted if the queues are running.
    """
    job_queue = ApiJobQueue(mocker.MagicMock(), mocker.MagicMock())
    mocker.patch.object(job_queue.main_queue, "resume")
    mocker.patch.object(job_queue.download_file_queue, "resume")
    job_queue.main_thread.isRunning = mocker.MagicMock(return_value=True)
    job_queue.download_file_thread.isRunning = mocker.MagicMock(return_value=True)

    job_queue.resume_queues()

    job_queue.main_queue.resume.emit.assert_called_once_with()
    job_queue.download_file_queue.resume.emit.assert_called_once_with()


def test_ApiJobQueue_resume_queues_does_not_emit_resume_signal_if_queues_are_not_running(mocker):
    """
    Ensure resume signal is not emitted if the queues ar not running.
    """
    job_queue = ApiJobQueue(mocker.MagicMock(), mocker.MagicMock())
    mocker.patch.object(job_queue.main_queue, "resume")
    mocker.patch.object(job_queue.download_file_queue, "resume")
    job_queue.main_thread.isRunning = mocker.MagicMock(return_value=False)
    job_queue.download_file_thread.isRunning = mocker.MagicMock(return_value=False)

    job_queue.resume_queues()

    job_queue.main_queue.resume.emit.assert_not_called()
    job_queue.download_file_queue.resume.emit.assert_not_called()


def test_ApiJobQueue_enqueue_no_auth(mocker):
    mock_client = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock()

    job_queue = ApiJobQueue(mock_client, mock_session_maker)
    mock_download_file_queue = mocker.patch.object(job_queue, "download_file_queue")
    mock_main_queue = mocker.patch.object(job_queue, "main_queue")
    mock_download_file_add_job = mocker.patch.object(mock_download_file_queue, "add_job")
    mock_main_queue_add_job = mocker.patch.object(mock_main_queue, "add_job")
    job_queue.main_queue.api_client = None
    job_queue.download_file_queue.api_client = None

    dummy_job = factory.dummy_job_factory(mocker, "mock")()
    job_queue.JOB_PRIORITIES = {type(dummy_job): 1}
    job_queue.enqueue(dummy_job)

    assert mock_download_file_add_job.call_count == 0
    assert mock_main_queue_add_job.call_count == 0


def test_ApiJobQueue_start_if_queues_not_running(mocker):
    """
    Ensure token is passed to the queues and that they are started.
    """
    mock_api = mocker.MagicMock()
    mock_client = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock()

    job_queue = ApiJobQueue(mock_client, mock_session_maker)

    mock_main_queue = mocker.patch.object(job_queue, "main_queue")
    mock_download_file_queue = mocker.patch.object(job_queue, "download_file_queue")
    mock_main_thread = mocker.patch.object(job_queue, "main_thread")
    mock_download_file_thread = mocker.patch.object(job_queue, "download_file_thread")
    job_queue.main_thread.isRunning = mocker.MagicMock(return_value=False)
    job_queue.download_file_thread.isRunning = mocker.MagicMock(return_value=False)

    job_queue.start(mock_api)

    assert mock_main_queue.api_client == mock_api
    assert mock_download_file_queue.api_client == mock_api

    mock_main_thread.start.assert_called_once_with()
    mock_download_file_thread.start.assert_called_once_with()


def test_ApiJobQueue_start_if_queues_running(mocker):
    """
    Ensure token is passed to the queues that are already started.
    """
    mock_api = mocker.MagicMock()
    mock_client = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock()

    job_queue = ApiJobQueue(mock_client, mock_session_maker)

    mock_main_queue = mocker.patch.object(job_queue, "main_queue")
    mock_download_file_queue = mocker.patch.object(job_queue, "download_file_queue")
    mock_main_thread = mocker.patch.object(job_queue, "main_thread")
    mock_download_file_thread = mocker.patch.object(job_queue, "download_file_thread")
    job_queue.main_thread.isRunning = mocker.MagicMock(return_value=True)
    job_queue.download_file_thread.isRunning = mocker.MagicMock(return_value=True)

    job_queue.start(mock_api)

    assert mock_main_queue.api_client == mock_api
    assert mock_download_file_queue.api_client == mock_api

    assert not mock_main_thread.start.called
    assert not mock_download_file_thread.start.called


def test_ApiJobQueue_stop_stops_queue_threads(mocker):
    job_queue = ApiJobQueue(mocker.MagicMock(), mocker.MagicMock())

    job_queue.stop()

    assert not job_queue.main_thread.isRunning()
    assert not job_queue.download_file_thread.isRunning()


def test_ApiJobQueue_stop_clears_jobs(mocker):
    """
    After ApiJobQueue.stop(), the underlying RunnableQueue is empty.
    """
    mock_api = mocker.MagicMock()
    mock_client = mocker.MagicMock()
    mock_session_maker = mocker.MagicMock()

    job_queue = ApiJobQueue(mock_client, mock_session_maker)
    job_queue.start(mock_api)

    job = SendReplyJob("mock", "mock", "mock", "mock")
    job_queue.enqueue(job)
    assert job_queue.main_queue.queue.qsize() == 1

    job_queue.stop()
    assert job_queue.main_queue.queue.empty()


def test_ApiJobQueue_stop_results_in_queue_threads_not_running(mocker):
    job_queue = ApiJobQueue(mocker.MagicMock(), mocker.MagicMock())
    job_queue.main_thread = mocker.MagicMock()
    job_queue.download_file_thread = mocker.MagicMock()

    job_queue.stop()

    job_queue.main_thread.quit.assert_called_once_with()
    job_queue.download_file_thread.quit.assert_called_once_with()
