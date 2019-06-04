import pytest

from sdclientapi import AuthError, RequestTimeoutError

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
