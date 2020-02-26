import pytest

from sdclientapi import AuthError, RequestTimeoutError, ServerConnectionError

from securedrop_client.api_jobs.base import ApiInaccessibleError, ApiJob
from tests.factory import dummy_job_factory


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


def test_ApiJob_comparison(mocker):
    return_value = 'wat'
    api_job_cls = dummy_job_factory(mocker, return_value)
    api_job_1 = api_job_cls()
    api_job_1.order_number = 1

    api_job_2 = api_job_cls()
    api_job_2.order_number = 2

    assert api_job_1 < api_job_2


def test_ApiJob_order_number_unset(mocker):
    return_value = 'wat'
    api_job_cls = dummy_job_factory(mocker, return_value)
    api_job_1 = api_job_cls()
    api_job_2 = api_job_cls()

    with pytest.raises(ValueError):
        api_job_1 < api_job_2
