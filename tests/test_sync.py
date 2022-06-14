import pytest
from sdclientapi import RequestTimeoutError, ServerConnectionError

from securedrop_client.api_jobs.base import ApiInaccessibleError
from securedrop_client.app import threads
from securedrop_client.sync import ApiSync


def test_ApiSync_init(mocker, session_maker, homedir):
    """
    Ensure sync thread is not started in the constructor.
    """
    with threads(1) as [sync_thread]:
        api_sync = ApiSync(
            mocker.MagicMock(), session_maker, mocker.MagicMock(), homedir, sync_thread
        )
        assert not api_sync.sync_thread.isRunning()


def test_ApiSync_start(mocker, session_maker, homedir):
    """
    Ensure sync thread starts when start is called and not already running.
    """
    with threads(1) as [sync_thread]:
        api_sync = ApiSync(
            mocker.MagicMock(), session_maker, mocker.MagicMock(), homedir, sync_thread
        )
        api_sync.sync_thread = mocker.MagicMock()
        api_sync.sync_thread.isRunning = mocker.MagicMock(return_value=False)

        api_sync.start(mocker.MagicMock())

        api_sync.sync_thread.start.assert_called_once_with()


def test_ApiSync_start_not_called_when_already_started(mocker, session_maker, homedir):
    """
    Ensure sync thread does not start when start is called if already running.
    """
    with threads(1) as [sync_thread]:
        api_sync = ApiSync(
            mocker.MagicMock(), session_maker, mocker.MagicMock(), homedir, sync_thread
        )
        api_sync.sync_thread = mocker.MagicMock()
        api_sync.sync_thread.isRunning = mocker.MagicMock(return_value=True)

        api_sync.start(mocker.MagicMock())

        api_sync.sync_thread.start.assert_not_called()


def test_ApiSync_stop(mocker, session_maker, homedir):
    """
    Ensure thread is not running when stopped and api_client is None.
    """
    with threads(1) as [sync_thread]:
        api_sync = ApiSync(
            mocker.MagicMock(), session_maker, mocker.MagicMock(), homedir, sync_thread
        )

        api_sync.stop()

        assert api_sync.api_client is None
        assert not api_sync.sync_thread.isRunning()


def test_ApiSync_stop_calls_quit(mocker, session_maker, homedir):
    """
    Ensure stop calls QThread's quit method and api_client is None.
    """
    with threads(1) as [sync_thread]:
        api_sync = ApiSync(
            mocker.MagicMock(), session_maker, mocker.MagicMock(), homedir, sync_thread
        )
        api_sync.sync_thread = mocker.MagicMock()
        api_sync.sync_thread.isRunning = mocker.MagicMock(return_value=True)

        api_sync.stop()

        assert api_sync.api_client is None
        api_sync.sync_thread.quit.assert_called_once_with()


def test_ApiSync_sync_starts_now(mocker, session_maker, homedir):
    """
    Ensure ApiSync sync() starts immediate single-shot sync
    QTimer.singleShot(1, self.api_sync_bg_task.sync)
    """
    with threads(1) as [sync_thread]:
        api_sync = ApiSync(
            mocker.MagicMock(), session_maker, mocker.MagicMock(), homedir, sync_thread
        )

        mock_qtimer = mocker.MagicMock()
        mocker.patch("securedrop_client.sync.QTimer", mock_qtimer)
        mock_singleshot_method = mocker.MagicMock()
        mock_qtimer.singleShot = mock_singleshot_method

        api_sync.sync()

        mock_singleshot_method.assert_called_once_with(1, api_sync.api_sync_bg_task.sync)


def test_ApiSyncBackgroundTask_sync(mocker, session_maker, homedir):
    """
    Ensure sync enqueues a MetadataSyncJob and calls it's parent's processing function
    """
    api_client = mocker.MagicMock()
    with threads(1) as [sync_thread]:
        api_sync = ApiSync(api_client, session_maker, mocker.MagicMock(), homedir, sync_thread)
        sync_started = mocker.patch.object(api_sync.api_sync_bg_task, "sync_started")
        _do_call_api_fn = mocker.patch("securedrop_client.sync.MetadataSyncJob._do_call_api")

        api_sync.api_sync_bg_task.sync()

        sync_started.emit.assert_called_once_with()
        assert _do_call_api_fn.called


def test_ApiSyncBackgroundTask_sync_resets_retries(mocker, session_maker, homedir):
    """
    Ensure sync enqueues a MetadataSyncJob and calls it's parent's processing function
    """
    api_client = mocker.MagicMock()
    with threads(1) as [sync_thread]:
        api_sync = ApiSync(api_client, session_maker, mocker.MagicMock(), homedir, sync_thread)

        api_sync.api_sync_bg_task.sync()
        assert api_sync.api_sync_bg_task.job.remaining_attempts == 1

        api_sync.api_sync_bg_task.sync()
        assert api_sync.api_sync_bg_task.job.remaining_attempts == 1


def test_ApiSyncBackgroundTask_sync_catches_ApiInaccessibleError(mocker, session_maker, homedir):
    """
    Ensure sync calls the parent processing function of MetadataSyncJob, catches
    ApiInaccessibleError exception, and emits failure signal.
    """
    api_client = mocker.MagicMock()
    with threads(1) as [sync_thread]:
        api_sync = ApiSync(api_client, session_maker, mocker.MagicMock(), homedir, sync_thread)
        sync_started = mocker.patch.object(api_sync.api_sync_bg_task, "sync_started")
        success_signal = mocker.patch("securedrop_client.sync.MetadataSyncJob.success_signal")
        failure_signal = mocker.patch("securedrop_client.sync.MetadataSyncJob.failure_signal")
        error = ApiInaccessibleError()
        _do_call_api_fn = mocker.patch(
            "securedrop_client.sync.MetadataSyncJob._do_call_api", side_effect=error
        )

        api_sync.api_sync_bg_task.sync()

        assert _do_call_api_fn.called
        sync_started.emit.assert_called_once_with()
        success_signal.emit.assert_not_called()
        failure_signal.emit.assert_called_once_with(error)


def test_ApiSyncBackgroundTask_sync_catches_all_other_exceptions(mocker, session_maker, homedir):
    """
    Ensure sync calls the parent processing function of MetadataSyncJob, catches all exceptions,
    and emits failure signal.
    """
    api_client = mocker.MagicMock()
    with threads(1) as [sync_thread]:
        api_sync = ApiSync(api_client, session_maker, mocker.MagicMock(), homedir, sync_thread)
        sync_started = mocker.patch.object(api_sync.api_sync_bg_task, "sync_started")
        success_signal = mocker.patch("securedrop_client.sync.MetadataSyncJob.success_signal")
        failure_signal = mocker.patch("securedrop_client.sync.MetadataSyncJob.failure_signal")
        error = Exception()
        call_api_fn = mocker.patch(
            "securedrop_client.sync.MetadataSyncJob.call_api", side_effect=error
        )

        api_sync.api_sync_bg_task.sync()

        assert call_api_fn.called
        sync_started.emit.assert_called_once_with()
        success_signal.emit.assert_not_called()
        failure_signal.emit.assert_called_once_with(error)


def test_ApiSync_on_sync_success(mocker, session_maker, homedir):
    """
    Ensure success handler emits success signal that the Controller links to and fires another sync
    after a supplied amount of time.
    """
    with threads(1) as [sync_thread]:
        api_sync = ApiSync(
            mocker.MagicMock(), session_maker, mocker.MagicMock(), homedir, sync_thread
        )
        sync_success = mocker.patch.object(api_sync, "sync_success")

        api_sync.on_sync_success()

        sync_success.emit.assert_called_once_with()


def test_ApiSync_on_sync_failure(mocker, session_maker, homedir):
    """
    Ensure failure handler emits failure signal that the Controller links to and does not fire
    another sync for errors other than RequestTimeoutError or ServerConnectionError
    """
    with threads(1) as [sync_thread]:
        api_sync = ApiSync(
            mocker.MagicMock(), session_maker, mocker.MagicMock(), homedir, sync_thread
        )
        sync_failure = mocker.patch.object(api_sync, "sync_failure")

        error = Exception()

        api_sync.on_sync_failure(error)

        sync_failure.emit.assert_called_once_with(error)


@pytest.mark.parametrize("exception", [RequestTimeoutError, ServerConnectionError])
def test_ApiSync_on_sync_failure_because_of_timeout(mocker, session_maker, homedir, exception):
    """
    Ensure failure handler emits failure signal that the Controller links to and sets up timer to
    fire another sync after 15 seconds if the failure reason is a RequestTimeoutError or
    ServerConnectionError.
    """
    with threads(1) as [sync_thread]:
        api_sync = ApiSync(
            mocker.MagicMock(), session_maker, mocker.MagicMock(), homedir, sync_thread
        )
        sync_failure = mocker.patch.object(api_sync, "sync_failure")
        error = exception()

        api_sync.on_sync_failure(error)

        sync_failure.emit.assert_called_once_with(error)
