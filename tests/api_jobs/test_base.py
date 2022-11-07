import pytest
from sdclientapi import AuthError, RequestTimeoutError, ServerConnectionError

from securedrop_client.api_jobs.base import ApiInaccessibleError, ApiJob, SingleObjectApiJob
from tests.factory import dummy_job_factory


def test_ApiInaccessibleError_init():
    # check default value
    err = ApiInaccessibleError()
    assert str(err).startswith("API is inaccessible")
    assert isinstance(err, Exception)

    # check custom
    msg = "foo"
    err = ApiInaccessibleError(msg)
    assert str(err) == msg


def test_ApiJob_raises_NotImplementedError():
    job = ApiJob()

    with pytest.raises(NotImplementedError):
        job.call_api(None, None)


def test_ApiJob_no_api(mocker):
    return_value = "wat"
    api_job_cls = dummy_job_factory(mocker, return_value)
    api_job = api_job_cls()

    mock_session = mocker.MagicMock()

    with pytest.raises(ApiInaccessibleError):
        api_job._do_call_api(None, mock_session)

    assert not api_job.success_signal.emit.called
    assert not api_job.failure_signal.emit.called


def test_ApiJob_success(mocker):
    return_value = "wat"
    api_job_cls = dummy_job_factory(mocker, return_value)
    api_job = api_job_cls()

    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    api_job._do_call_api(mock_api_client, mock_session)

    api_job.success_signal.emit.assert_called_once_with(return_value)
    assert not api_job.failure_signal.emit.called


def test_ApiJob_auth_error(mocker):
    return_value = AuthError("oh no")
    api_job_cls = dummy_job_factory(mocker, return_value)
    api_job = api_job_cls()

    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    with pytest.raises(ApiInaccessibleError):
        api_job._do_call_api(mock_api_client, mock_session)

    assert not api_job.success_signal.emit.called
    assert not api_job.failure_signal.emit.called


@pytest.mark.parametrize("exception", [RequestTimeoutError, ServerConnectionError])
def test_ApiJob_timeout_error(mocker, exception):
    """If the server times out or is unreachable, the corresponding
    exception should be raised"""
    return_value = exception()
    api_job_cls = dummy_job_factory(mocker, return_value)
    api_job = api_job_cls()

    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    with pytest.raises(exception):
        api_job._do_call_api(mock_api_client, mock_session)

    assert not api_job.success_signal.emit.called
    assert api_job.failure_signal.emit.called


def test_ApiJob_other_error(mocker):
    return_value = Exception()
    api_job_cls = dummy_job_factory(mocker, return_value)
    api_job = api_job_cls()

    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    with pytest.raises(Exception):
        api_job._do_call_api(mock_api_client, mock_session)

    assert not api_job.success_signal.emit.called
    api_job.failure_signal.emit.assert_called_once_with(return_value)


@pytest.mark.parametrize("exception", [RequestTimeoutError, ServerConnectionError])
def test_ApiJob_retry_succeeds_after_failed_attempt(mocker, exception):
    """Retry logic: after failed attempt should succeed"""

    number_of_attempts = 5
    success_return_value = "now works"
    return_values = [exception(), success_return_value]
    api_job_cls = dummy_job_factory(mocker, return_values, remaining_attempts=number_of_attempts)
    api_job = api_job_cls()

    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    api_job._do_call_api(mock_api_client, mock_session)

    assert api_job.remaining_attempts == number_of_attempts - 2

    assert not api_job.failure_signal.emit.called
    api_job.success_signal.emit.assert_called_once_with(success_return_value)


@pytest.mark.parametrize("exception", [RequestTimeoutError, ServerConnectionError])
def test_ApiJob_retry_exactly_n_attempts_times(mocker, exception):
    """Retry logic: boundary value case - 5th attempt should succeed"""

    number_of_attempts = 5
    success_return_value = "now works"
    return_values = [exception()] * (number_of_attempts - 1) + [success_return_value]
    api_job_cls = dummy_job_factory(mocker, return_values, remaining_attempts=number_of_attempts)
    api_job = api_job_cls()

    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    api_job._do_call_api(mock_api_client, mock_session)

    assert api_job.remaining_attempts == 0

    assert not api_job.failure_signal.emit.called
    api_job.success_signal.emit.assert_called_once_with(success_return_value)


@pytest.mark.parametrize("exception", [RequestTimeoutError, ServerConnectionError])
def test_ApiJob_retry_timeout(mocker, exception):
    """Retry logic: If we exceed the number of attempts, the job will still fail"""

    number_of_attempts = 5
    return_values = [exception()] * (number_of_attempts + 1)
    api_job_cls = dummy_job_factory(mocker, return_values, remaining_attempts=number_of_attempts)
    api_job = api_job_cls()

    mock_api_client = mocker.MagicMock()
    mock_session = mocker.MagicMock()

    with pytest.raises(exception):
        api_job._do_call_api(mock_api_client, mock_session)

    assert api_job.remaining_attempts == 0

    assert not api_job.success_signal.emit.called
    assert api_job.failure_signal.emit.called


def test_ApiJob_comparison(mocker):
    return_value = "wat"
    api_job_cls = dummy_job_factory(mocker, return_value)
    api_job_1 = api_job_cls()
    api_job_1.order_number = 1

    api_job_2 = api_job_cls()
    api_job_2.order_number = 2

    assert api_job_1 < api_job_2


def test_ApiJob_order_number_unset(mocker):
    return_value = "wat"
    api_job_cls = dummy_job_factory(mocker, return_value)
    api_job_1 = api_job_cls()
    api_job_2 = api_job_cls()

    with pytest.raises(ValueError):
        api_job_1 < api_job_2


def test_SingleObjectApiJob_comparison_obj_without_uuid_attr(mocker):
    test_job_with_uuid = SingleObjectApiJob("uuid1")
    test_job_without_uuid = ApiJob()

    assert test_job_with_uuid != test_job_without_uuid


def test_SingleObjectApiJob_comparison_obj_with_uuid_attr(mocker):
    test_job_with_uuid = SingleObjectApiJob("uuid1")
    test_job_with_uuid_2 = SingleObjectApiJob("uuid1")

    assert test_job_with_uuid == test_job_with_uuid_2
