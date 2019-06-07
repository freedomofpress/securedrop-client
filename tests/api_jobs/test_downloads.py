import os
from typing import Tuple

import pytest
import sdclientapi
from sdclientapi import BaseError

from securedrop_client.api_jobs.downloads import DownloadJob, FileDownloadJob, MessageDownloadJob
from securedrop_client.crypto import GpgHelper, CryptoError
from tests import factory


def test_DownloadJob_raises_NotImplemetedError(mocker):
    job = DownloadJob(mocker.MagicMock(), 'mock', mocker.MagicMock(), 'mock')

    with pytest.raises(NotImplementedError):
        job.call_api_download(mocker.Mock(), mocker.Mock(), mocker.Mock())


def test_MessageDownloadJob_no_download_or_decrypt(mocker, homedir, session, session_maker):
    """
    Test that an already-downloaded message successfully decrypts. Use the `homedir` fixture to get
    a GPG keyring.
    """
    message = factory.Message(
        source=factory.Source(), is_downloaded=True, is_decrypted=True, content=None)
    session.add(message)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    gpg.decrypt_submission_or_reply = mocker.MagicMock()
    api_client = mocker.MagicMock()
    path = os.path.join(homedir, 'mock_filename')
    api_client.download_submission = mocker.MagicMock(return_value=('mock_etag', path))
    debug_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger.debug')

    job = MessageDownloadJob(message.uuid, homedir, gpg)
    job.call_api(api_client, session)

    api_client.download_submission.assert_not_called()
    gpg.decrypt_submission_or_reply.assert_not_called()
    assert message.is_downloaded is True
    assert message.is_decrypted is True
    msg_1 = 'Already downloaded {}'.format(message.filename)
    msg_2 = 'Already decrypted {}'.format(message.filename)
    debug_logger.assert_has_calls([mocker.call(msg_1), mocker.call(msg_2)])


def test_MessageDownloadJob_download_and_decrypt(mocker, homedir, session, session_maker):
    """
    Test when a message successfully downloads and decrypts. Use the `homedir` fixture to get a GPG
    keyring.
    """
    message_first_download_attempt = factory.Message(
        source=factory.Source(), is_downloaded=None, is_decrypted=None, content=None)
    message_next_download_attempt = factory.Message(
        source=factory.Source(), is_downloaded=False, is_decrypted=None, content=None)
    session.add(message_first_download_attempt)
    session.add(message_next_download_attempt)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    gpg.decrypt_submission_or_reply = mocker.MagicMock()
    api_client = mocker.MagicMock()
    path = os.path.join(homedir, 'mock_filename')
    api_client.download_submission = mocker.MagicMock(return_value=('mock_etag', path))
    debug_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger.debug')

    job_1 = MessageDownloadJob(message_first_download_attempt.uuid, homedir, gpg)
    job_1.call_api(api_client, session)
    job_2 = MessageDownloadJob(message_next_download_attempt.uuid, homedir, gpg)
    job_2.call_api(api_client, session)

    assert api_client.download_submission.called
    assert gpg.decrypt_submission_or_reply.called
    assert message_first_download_attempt.is_downloaded is True
    assert message_next_download_attempt.is_downloaded is True
    assert message_first_download_attempt.is_decrypted is True
    assert message_next_download_attempt.is_decrypted is True
    assert message_first_download_attempt.content is not None
    assert message_next_download_attempt.content is not None
    msg_1 = 'Downloaded {}'.format(message_first_download_attempt.filename)
    msg_2 = 'Decrypted {}'.format(message_first_download_attempt.filename)
    msg_3 = 'Downloaded {}'.format(message_next_download_attempt.filename)
    msg_4 = 'Decrypted {}'.format(message_next_download_attempt.filename)
    debug_logger.assert_has_calls([
        mocker.call(msg_1), mocker.call(msg_2), mocker.call(msg_3), mocker.call(msg_4)])


def test_MessageDownloadJob_only_decrypt(mocker, homedir, session, session_maker):
    """
    Test that an already-downloaded message successfully decrypts. Use the `homedir` fixture to get
    a GPG keyring.
    """
    message_first_decrypt_attempt = factory.Message(
        source=factory.Source(), is_downloaded=True, is_decrypted=None, content=None)
    message_next_decrypt_attempt = factory.Message(
        source=factory.Source(), is_downloaded=True, is_decrypted=False, content=None)
    session.add(message_first_decrypt_attempt)
    session.add(message_next_decrypt_attempt)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    gpg.decrypt_submission_or_reply = mocker.MagicMock()
    api_client = mocker.MagicMock()
    path = os.path.join(homedir, 'mock_filename')
    api_client.download_submission = mocker.MagicMock(return_value=('mock_etag', path))
    debug_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger.debug')

    job_1 = MessageDownloadJob(message_first_decrypt_attempt.uuid, homedir, gpg)
    job_1.call_api(api_client, session)
    job_2 = MessageDownloadJob(message_next_decrypt_attempt.uuid, homedir, gpg)
    job_2.call_api(api_client, session)

    api_client.download_submission.assert_not_called()
    assert gpg.decrypt_submission_or_reply.called
    assert message_first_decrypt_attempt.is_downloaded is True
    assert message_next_decrypt_attempt.is_downloaded is True
    assert message_first_decrypt_attempt.is_decrypted is True
    assert message_next_decrypt_attempt.is_decrypted is True
    assert message_first_decrypt_attempt.content is not None
    assert message_next_decrypt_attempt.content is not None
    msg_1 = 'Already downloaded {}'.format(message_first_decrypt_attempt.filename)
    msg_2 = 'Decrypted {}'.format(message_first_decrypt_attempt.filename)
    msg_3 = 'Already downloaded {}'.format(message_next_decrypt_attempt.filename)
    msg_4 = 'Decrypted {}'.format(message_next_decrypt_attempt.filename)
    debug_logger.assert_has_calls([
        mocker.call(msg_1), mocker.call(msg_2), mocker.call(msg_3), mocker.call(msg_4)])


def test_MessageDownloadJob_download_with_download_error(mocker, homedir, session, session_maker):
    """
    Test when a message does not successfully download.
    """
    message_first_download_attempt = factory.Message(
        source=factory.Source(), is_downloaded=None, is_decrypted=None, content=None)
    message_next_download_attempt = factory.Message(
        source=factory.Source(), is_downloaded=False, is_decrypted=None, content=None)
    session.add(message_first_download_attempt)
    session.add(message_next_download_attempt)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    gpg.decrypt_submission_or_reply = mocker.MagicMock()
    api_client = mocker.MagicMock()
    path = os.path.join(homedir, 'mock_filename')
    api_client.download_submission = mocker.MagicMock(
        return_value=('mock_etag', path), side_effect=BaseError('mock_err'))
    debug_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger.debug')

    with pytest.raises(BaseError):
        job_1 = MessageDownloadJob(message_first_download_attempt.uuid, homedir, gpg)
        job_1.call_api(api_client, session)
    with pytest.raises(BaseError):
        job_2 = MessageDownloadJob(message_next_download_attempt.uuid, homedir, gpg)
        job_2.call_api(api_client, session)

    assert api_client.download_submission.called
    gpg.decrypt_submission_or_reply.assert_not_called()
    assert message_first_download_attempt.is_downloaded is False
    assert message_next_download_attempt.is_downloaded is False
    assert message_first_download_attempt.is_decrypted is None
    assert message_next_download_attempt.is_decrypted is None
    assert message_first_download_attempt.content is None
    assert message_next_download_attempt.content is None
    msg_1 = 'Failed to download {}: {}'.format(message_first_download_attempt.filename, 'mock_err')
    msg_2 = 'Failed to download {}: {}'.format(message_next_download_attempt.filename, 'mock_err')
    debug_logger.assert_has_calls([mocker.call(msg_1), mocker.call(msg_2)])


def test_MessageDownloadJob_first_download_w_decrypt_error(mocker, homedir, session, session_maker):
    """
    Test when a message does not successfully decrypt after a successful download.
    """
    message_first_decrypt_attempt = factory.Message(
        source=factory.Source(), is_downloaded=True, is_decrypted=None, content=None)
    message_next_decrypt_attempt = factory.Message(
        source=factory.Source(), is_downloaded=True, is_decrypted=False, content=None)
    session.add(message_first_decrypt_attempt)
    session.add(message_next_decrypt_attempt)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    gpg.decrypt_submission_or_reply = mocker.MagicMock(side_effect=CryptoError('mock_error'))
    api_client = mocker.MagicMock()
    path = os.path.join(homedir, 'mock_filename')
    api_client.download_submission = mocker.MagicMock(return_value=('mock_etag', path))
    debug_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger.debug')

    with pytest.raises(CryptoError):
        job_1 = MessageDownloadJob(message_first_decrypt_attempt.uuid, homedir, gpg)
        job_1.call_api(api_client, session)
    with pytest.raises(CryptoError):
        job_2 = MessageDownloadJob(message_next_decrypt_attempt.uuid, homedir, gpg)
        job_2.call_api(api_client, session)

    api_client.download_submission.assert_not_called()
    assert gpg.decrypt_submission_or_reply.called
    assert message_first_decrypt_attempt.is_downloaded is True
    assert message_next_decrypt_attempt.is_downloaded is True
    assert message_first_decrypt_attempt.is_decrypted is False
    assert message_next_decrypt_attempt.is_decrypted is False
    assert message_first_decrypt_attempt.content is None
    assert message_next_decrypt_attempt.content is None
    msg_1 = 'Already downloaded {}'.format(message_first_decrypt_attempt.filename)
    msg_2 = 'Failed to decrypt {}: {}'.format(message_first_decrypt_attempt.filename, 'mock_error')
    msg_3 = 'Already downloaded {}'.format(message_next_decrypt_attempt.filename)
    msg_4 = 'Failed to decrypt {}: {}'.format(message_next_decrypt_attempt.filename, 'mock_error')
    debug_logger.assert_has_calls([
        mocker.call(msg_1), mocker.call(msg_2), mocker.call(msg_3), mocker.call(msg_4)])


def test_MessageDownloadJob_next_download_w_decrypt_error(mocker, homedir, session, session_maker):
    """
    Test when a message does not successfully decrypt after a failed download.
    """
    message_first_decrypt_attempt = factory.Message(
        source=factory.Source(), is_downloaded=False, is_decrypted=None, content=None)
    message_next_decrypt_attempt = factory.Message(
        source=factory.Source(), is_downloaded=None, is_decrypted=None, content=None)
    session.add(message_first_decrypt_attempt)
    session.add(message_next_decrypt_attempt)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    gpg.decrypt_submission_or_reply = mocker.MagicMock(side_effect=CryptoError('mock_error'))
    api_client = mocker.MagicMock()
    path = os.path.join(homedir, 'mock_filename')
    api_client.download_submission = mocker.MagicMock(return_value=('mock_etag', path))
    debug_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger.debug')

    with pytest.raises(CryptoError):
        job_1 = MessageDownloadJob(message_first_decrypt_attempt.uuid, homedir, gpg)
        job_1.call_api(api_client, session)
    with pytest.raises(CryptoError):
        job_2 = MessageDownloadJob(message_next_decrypt_attempt.uuid, homedir, gpg)
        job_2.call_api(api_client, session)

    assert api_client.download_submission.called
    assert gpg.decrypt_submission_or_reply.called
    assert message_first_decrypt_attempt.is_downloaded is True
    assert message_next_decrypt_attempt.is_downloaded is True
    assert message_first_decrypt_attempt.is_decrypted is False
    assert message_next_decrypt_attempt.is_decrypted is False
    assert message_first_decrypt_attempt.content is None
    assert message_next_decrypt_attempt.content is None
    msg_1 = 'Downloaded {}'.format(message_first_decrypt_attempt.filename)
    msg_2 = 'Failed to decrypt {}: {}'.format(message_first_decrypt_attempt.filename, 'mock_error')
    msg_3 = 'Downloaded {}'.format(message_next_decrypt_attempt.filename)
    msg_4 = 'Failed to decrypt {}: {}'.format(message_next_decrypt_attempt.filename, 'mock_error')
    debug_logger.assert_has_calls([
        mocker.call(msg_1), mocker.call(msg_2), mocker.call(msg_3), mocker.call(msg_4)])


def test_FileDownloadJob_no_download_or_decrypt(mocker, homedir, session, session_maker):
    """
    Test that an already-downloaded message successfully decrypts. Use the `homedir` fixture to get
    a GPG keyring.
    """
    file = factory.File(source=factory.Source(), is_downloaded=True, is_decrypted=True)
    session.add(file)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    gpg.decrypt_submission_or_reply = mocker.MagicMock()
    api_client = mocker.MagicMock()
    path = os.path.join(homedir, 'mock_filename')
    api_client.download_submission = mocker.MagicMock(return_value=('mock_etag', path))
    debug_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger.debug')

    job = FileDownloadJob(file.uuid, homedir, gpg)
    job.call_api(api_client, session)

    api_client.download_submission.assert_not_called()
    gpg.decrypt_submission_or_reply.assert_not_called()
    assert file.is_downloaded is True
    assert file.is_decrypted is True
    msg_1 = 'Already downloaded {}'.format(file.filename)
    msg_2 = 'Already decrypted {}'.format(file.filename)
    debug_logger.assert_has_calls([mocker.call(msg_1), mocker.call(msg_2)])


def test_FileDownloadJob_download_and_decrypt(mocker, homedir, session, session_maker):
    """
    Test when a message successfully downloads and decrypts. Use the `homedir` fixture to get a GPG
    keyring.
    """
    file_first_download_attempt = factory.File(
        source=factory.Source(), is_downloaded=None, is_decrypted=None)
    file_next_download_attempt = factory.File(
        source=factory.Source(), is_downloaded=False, is_decrypted=None)
    session.add(file_first_download_attempt)
    session.add(file_next_download_attempt)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    gpg.decrypt_submission_or_reply = mocker.MagicMock()
    api_client = mocker.MagicMock()
    path = os.path.join(homedir, 'mock_filename')
    api_client.download_submission = mocker.MagicMock(return_value=('', path))  # no etag
    debug_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger.debug')

    job_1 = FileDownloadJob(file_first_download_attempt.uuid, homedir, gpg)
    job_1.call_api(api_client, session)
    job_2 = FileDownloadJob(file_next_download_attempt.uuid, homedir, gpg)
    job_2.call_api(api_client, session)

    assert api_client.download_submission.called
    assert gpg.decrypt_submission_or_reply.called
    assert file_first_download_attempt.is_downloaded is True
    assert file_next_download_attempt.is_downloaded is True
    assert file_first_download_attempt.is_decrypted is True
    assert file_next_download_attempt.is_decrypted is True
    assert file_first_download_attempt.content is not None
    assert file_next_download_attempt.content is not None
    msg_1 = 'Downloaded {}'.format(file_first_download_attempt.filename)
    msg_2 = 'No ETag. Skipping integrity check for file at {}'.format(path)
    msg_3 = 'Decrypted {}'.format(file_first_download_attempt.filename)
    msg_4 = 'Downloaded {}'.format(file_next_download_attempt.filename)
    msg_5 = 'No ETag. Skipping integrity check for file at {}'.format(path)
    msg_6 = 'Decrypted {}'.format(file_next_download_attempt.filename)
    debug_logger.assert_has_calls([
        mocker.call(msg_1), mocker.call(msg_2), mocker.call(msg_3),
        mocker.call(msg_4), mocker.call(msg_5), mocker.call(msg_6)])


def test_FileDownloadJob_only_decrypt(mocker, homedir, session, session_maker):
    """
    Test that an already-downloaded message successfully decrypts. Use the `homedir` fixture to get
    a GPG keyring.
    """
    file_first_decrypt_attempt = factory.File(
        source=factory.Source(), is_downloaded=True, is_decrypted=None)
    file_next_decrypt_attempt = factory.File(
        source=factory.Source(), is_downloaded=True, is_decrypted=False)
    session.add(file_first_decrypt_attempt)
    session.add(file_next_decrypt_attempt)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    gpg.decrypt_submission_or_reply = mocker.MagicMock()
    api_client = mocker.MagicMock()
    path = os.path.join(homedir, 'mock_filename')
    api_client.download_submission = mocker.MagicMock(return_value=('', path))
    debug_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger.debug')

    job_1 = FileDownloadJob(file_first_decrypt_attempt.uuid, homedir, gpg)
    job_1.call_api(api_client, session)
    job_2 = FileDownloadJob(file_next_decrypt_attempt.uuid, homedir, gpg)
    job_2.call_api(api_client, session)

    api_client.download_submission.assert_not_called()
    assert gpg.decrypt_submission_or_reply.called
    assert file_first_decrypt_attempt.is_downloaded is True
    assert file_next_decrypt_attempt.is_downloaded is True
    assert file_first_decrypt_attempt.is_decrypted is True
    assert file_next_decrypt_attempt.is_decrypted is True
    assert file_first_decrypt_attempt.content is not None
    assert file_next_decrypt_attempt.content is not None
    msg_1 = 'Already downloaded {}'.format(file_first_decrypt_attempt.filename)
    msg_2 = 'Decrypted {}'.format(file_first_decrypt_attempt.filename)
    msg_3 = 'Already downloaded {}'.format(file_next_decrypt_attempt.filename)
    msg_4 = 'Decrypted {}'.format(file_next_decrypt_attempt.filename)
    debug_logger.assert_has_calls([
        mocker.call(msg_1), mocker.call(msg_2), mocker.call(msg_3), mocker.call(msg_4)])


def test_FileDownloadJob_download_with_download_error(mocker, homedir, session, session_maker):
    """
    Test when a message does not successfully download.
    """
    file_first_download_attempt = factory.File(
        source=factory.Source(), is_downloaded=None, is_decrypted=None)
    file_next_download_attempt = factory.File(
        source=factory.Source(), is_downloaded=False, is_decrypted=None)
    session.add(file_first_download_attempt)
    session.add(file_next_download_attempt)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    gpg.decrypt_submission_or_reply = mocker.MagicMock()
    api_client = mocker.MagicMock()
    path = os.path.join(homedir, 'mock_filename')
    api_client.download_submission = mocker.MagicMock(
        return_value=('mock_etag', path), side_effect=BaseError('mock_error'))
    debug_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger.debug')

    with pytest.raises(BaseError):
        job_1 = FileDownloadJob(file_first_download_attempt.uuid, homedir, gpg)
        job_1.call_api(api_client, session)
    with pytest.raises(BaseError):
        job_2 = FileDownloadJob(file_next_download_attempt.uuid, homedir, gpg)
        job_2.call_api(api_client, session)

    assert api_client.download_submission.called
    gpg.decrypt_submission_or_reply.assert_not_called()
    assert file_first_download_attempt.is_downloaded is False
    assert file_next_download_attempt.is_downloaded is False
    assert file_first_download_attempt.is_decrypted is None
    assert file_next_download_attempt.is_decrypted is None
    with pytest.raises(AttributeError):
        assert file_first_download_attempt.content
        assert file_next_download_attempt.content
    msg_1 = 'Failed to download {}: {}'.format(file_first_download_attempt.filename, 'mock_error')
    msg_2 = 'Failed to download {}: {}'.format(file_next_download_attempt.filename, 'mock_error')
    debug_logger.assert_has_calls([mocker.call(msg_1), mocker.call(msg_2)])


def test_FileDownloadJob_first_download_w_decrypt_error(mocker, homedir, session, session_maker):
    """
    Test when a message does not successfully decrypt after a successful download.
    """
    file_first_decrypt_attempt = factory.File(
        source=factory.Source(), is_downloaded=True, is_decrypted=None)
    file_next_decrypt_attempt = factory.File(
        source=factory.Source(), is_downloaded=True, is_decrypted=False)
    session.add(file_first_decrypt_attempt)
    session.add(file_next_decrypt_attempt)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    gpg.decrypt_submission_or_reply = mocker.MagicMock(side_effect=CryptoError('mock_error'))
    api_client = mocker.MagicMock()
    path = os.path.join(homedir, 'mock_filename')
    api_client.download_submission = mocker.MagicMock(return_value=('mock_etag', path))
    debug_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger.debug')

    with pytest.raises(CryptoError):
        job_1 = FileDownloadJob(file_first_decrypt_attempt.uuid, homedir, gpg)
        job_1.call_api(api_client, session)
    with pytest.raises(CryptoError):
        job_2 = FileDownloadJob(file_next_decrypt_attempt.uuid, homedir, gpg)
        job_2.call_api(api_client, session)

    api_client.download_submission.assert_not_called()
    assert gpg.decrypt_submission_or_reply.called
    assert file_first_decrypt_attempt.is_downloaded is True
    assert file_next_decrypt_attempt.is_downloaded is True
    assert file_first_decrypt_attempt.is_decrypted is False
    assert file_next_decrypt_attempt.is_decrypted is False
    with pytest.raises(AttributeError):
        assert file_first_decrypt_attempt.content
        assert file_next_decrypt_attempt.content
    msg_1 = 'Already downloaded {}'.format(file_first_decrypt_attempt.filename)
    msg_2 = 'Failed to decrypt {}: {}'.format(file_first_decrypt_attempt.filename, 'mock_error')
    msg_3 = 'Already downloaded {}'.format(file_next_decrypt_attempt.filename)
    msg_4 = 'Failed to decrypt {}: {}'.format(file_next_decrypt_attempt.filename, 'mock_error')
    debug_logger.assert_has_calls([
        mocker.call(msg_1), mocker.call(msg_2), mocker.call(msg_3), mocker.call(msg_4)])


def test_FileDownloadJob_next_download_w_decrypt_error(mocker, homedir, session, session_maker):
    """
    Test when a message does not successfully decrypt after a failed download.
    """
    file_first_decrypt_attempt = factory.File(
        source=factory.Source(), is_downloaded=False, is_decrypted=None)
    file_next_decrypt_attempt = factory.File(
        source=factory.Source(), is_downloaded=None, is_decrypted=None)
    session.add(file_first_decrypt_attempt)
    session.add(file_next_decrypt_attempt)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    gpg.decrypt_submission_or_reply = mocker.MagicMock(side_effect=CryptoError('mock_error'))
    api_client = mocker.MagicMock()
    path = os.path.join(homedir, 'mock_filename')
    api_client.download_submission = mocker.MagicMock(return_value=('', path))  # no etag
    debug_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger.debug')

    with pytest.raises(CryptoError):
        job_1 = FileDownloadJob(file_first_decrypt_attempt.uuid, homedir, gpg)
        job_1.call_api(api_client, session)
    with pytest.raises(CryptoError):
        job_2 = FileDownloadJob(file_next_decrypt_attempt.uuid, homedir, gpg)
        job_2.call_api(api_client, session)

    assert api_client.download_submission.called
    assert gpg.decrypt_submission_or_reply.called
    assert file_first_decrypt_attempt.is_downloaded is True
    assert file_next_decrypt_attempt.is_downloaded is True
    assert file_first_decrypt_attempt.is_decrypted is False
    assert file_next_decrypt_attempt.is_decrypted is False
    with pytest.raises(AttributeError):
        assert file_first_decrypt_attempt.content
        assert file_next_decrypt_attempt.content
    msg_1 = 'Downloaded {}'.format(file_first_decrypt_attempt.filename)
    msg_2 = 'No ETag. Skipping integrity check for file at {}'.format(path)
    msg_3 = 'Failed to decrypt {}: {}'.format(file_first_decrypt_attempt.filename, 'mock_error')
    msg_4 = 'Downloaded {}'.format(file_next_decrypt_attempt.filename)
    msg_5 = 'No ETag. Skipping integrity check for file at {}'.format(path)
    msg_6 = 'Failed to decrypt {}: {}'.format(file_next_decrypt_attempt.filename, 'mock_error')
    debug_logger.assert_has_calls([
        mocker.call(msg_1), mocker.call(msg_2), mocker.call(msg_3),
        mocker.call(msg_4), mocker.call(msg_5), mocker.call(msg_6)])


def test_FileDownloadJob_no_etag(mocker, homedir, session, session_maker):
    file = factory.File(source=factory.Source(), is_downloaded=None, is_decrypted=None)
    session.add(file)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    gpg.decrypt_submission_or_reply = mocker.MagicMock()
    api_client = mocker.MagicMock()
    path = os.path.join(homedir, 'mock_filename')
    api_client.download_submission = mocker.MagicMock(return_value=('', path))  # no etag
    debug_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger.debug')

    job = FileDownloadJob(file.uuid, homedir, gpg)
    job.call_api(api_client, session)

    assert api_client.download_submission.called
    assert gpg.decrypt_submission_or_reply.called
    assert file.is_downloaded is True
    assert file.is_decrypted is True
    assert file.content is not None
    msg_1 = 'Downloaded {}'.format(file.filename)
    msg_2 = 'No ETag. Skipping integrity check for file at {}'.format(path)
    msg_3 = 'Decrypted {}'.format(file.filename)
    debug_logger.assert_has_calls([
        mocker.call(msg_1), mocker.call(msg_2), mocker.call(msg_3)])


def test_FileDownloadJob_sha256_etag(mocker, homedir, session, session_maker):
    file = factory.File(source=factory.Source(), is_downloaded=None, is_decrypted=None)
    session.add(file)
    session.commit()
    assert file.is_downloaded is False
    assert file.is_decrypted is None
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    gpg.decrypt_submission_or_reply = mocker.MagicMock()
    api_client = mocker.MagicMock()
    path = os.path.join(homedir, 'mock_filename')

    # Create a stub that writes 'wat' to file and returns its actual sha256 hash
    def download_submission_stub(sdk_obj: sdclientapi.Submission) -> Tuple[str, str]:
        with open(path, 'wb') as f:
            f.write(b'wat')
        return ('sha256:f00a787f7492a95e165b470702f4fe9373583fbdc025b2c8bdf0262cc48fcff4', path)
    api_client.download_submission = download_submission_stub
    debug_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger.debug')

    job = FileDownloadJob(file.uuid, homedir, gpg)
    job.call_api(api_client, session)

    assert gpg.decrypt_submission_or_reply.called
    assert file.is_downloaded is True
    assert file.is_decrypted is True
    assert file.content is not None
    msg_1 = 'Downloaded {}'.format(file.filename)
    msg_2 = 'Decrypted {}'.format(file.filename)
    debug_logger.assert_has_calls([mocker.call(msg_1), mocker.call(msg_2)])


def test_FileDownloadJob_bad_sha256_etag(mocker, homedir, session, session_maker):
    file = factory.File(source=factory.Source(), is_downloaded=None, is_decrypted=None)
    session.add(file)
    session.commit()
    assert file.is_downloaded is False
    assert file.is_decrypted is None
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    gpg.decrypt_submission_or_reply = mocker.MagicMock()
    api_client = mocker.MagicMock()
    path = os.path.join(homedir, 'mock_filename')

    # Create a stub that writes 'wat' to file and returns the WRONG sha256 hash
    def download_submission_stub(sdk_obj: sdclientapi.Submission) -> Tuple[str, str]:
        with open(path, 'wb') as f:
            f.write(b'wat')
        return ('sha256:iamnotthechecksumforwat', path)
    api_client.download_submission = download_submission_stub
    debug_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger.debug')

    with pytest.raises(RuntimeError):
        job = FileDownloadJob(file.uuid, homedir, gpg)
        job.call_api(api_client, session)

    gpg.decrypt_submission_or_reply.assert_not_called()
    assert file.is_downloaded is True
    assert file.is_decrypted is None
    with pytest.raises(AttributeError):
        assert file.content
    debug_logger.assert_called_once_with('Downloaded {}'.format(file.filename))


def test_FileDownloadJob_unknown_etag(mocker, homedir, session, session_maker):
    file = factory.File(source=factory.Source(), is_downloaded=None, is_decrypted=None)
    session.add(file)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    gpg.decrypt_submission_or_reply = mocker.MagicMock()
    api_client = mocker.MagicMock()
    path = os.path.join(homedir, 'mock_filename')
    api_client.download_submission = mocker.MagicMock(return_value=('UNKNOWN:abc123', path))
    debug_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger.debug')

    job = FileDownloadJob(file.uuid, homedir, gpg)
    job.call_api(api_client, session)

    assert api_client.download_submission.called
    assert gpg.decrypt_submission_or_reply.called
    assert file.is_downloaded is True
    assert file.is_decrypted is True
    assert file.content is not None
    msg_1 = 'Downloaded {}'.format(file.filename)
    msg_2 = 'Unknown hash algorithm ({}). Skipping integrity check for file at {}'.format(
        'UNKNOWN', path)
    msg_3 = 'Decrypted {}'.format(file.filename)
    debug_logger.assert_has_calls([mocker.call(msg_1), mocker.call(msg_2), mocker.call(msg_3)])
