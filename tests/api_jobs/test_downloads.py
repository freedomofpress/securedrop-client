import os
import pytest
import sdclientapi
from typing import Tuple

from securedrop_client import db
from securedrop_client.api_jobs.downloads import FileDownloadJob, MessageDownloadJob
from securedrop_client.crypto import GpgHelper, CryptoError
from tests import factory


def test_MessageDownloadJob_happy_path(mocker, homedir, session, session_maker):
    """
    Test that an already-downloaded message successfully decrypts. Use the `homedir` fixture to get
    a GPG keyring.
    """
    message_is_decrypted_false = factory.Message(
        source=factory.Source(), is_downloaded=True, is_decrypted=False, content=None)
    message_is_decrypted_none = factory.Message(
        source=factory.Source(), is_downloaded=True, is_decrypted=None, content=None)
    session.add(message_is_decrypted_false)
    session.add(message_is_decrypted_none)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job_1 = MessageDownloadJob(message_is_decrypted_false.uuid, homedir, gpg)
    job_2 = MessageDownloadJob(message_is_decrypted_none.uuid, homedir, gpg)
    mocker.patch.object(job_1.gpg, 'decrypt_submission_or_reply')
    mocker.patch.object(job_2.gpg, 'decrypt_submission_or_reply')
    api_client = mocker.MagicMock()
    path = os.path.join(homedir, 'data')
    api_client.download_submission = mocker.MagicMock(return_value=('', path))

    job_1.call_api(api_client, session)
    job_2.call_api(api_client, session)

    assert message_is_decrypted_false.content is not None
    assert message_is_decrypted_false.is_downloaded is True
    assert message_is_decrypted_false.is_decrypted is True
    assert message_is_decrypted_none.content is not None
    assert message_is_decrypted_none.is_downloaded is True
    assert message_is_decrypted_none.is_decrypted is True


def test_MessageDownloadJob_message_already_decrypted(mocker, homedir, session, session_maker):
    """
    Test that call_api just returns uuid if already decrypted.
    """
    message = factory.Message(source=factory.Source(), is_downloaded=True, is_decrypted=True)
    session.add(message)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = MessageDownloadJob(message.uuid, homedir, gpg)
    decrypt_fn = mocker.patch.object(job.gpg, 'decrypt_submission_or_reply')
    api_client = mocker.MagicMock()
    download_fn = mocker.patch.object(api_client, 'download_submission')

    return_uuid = job.call_api(api_client, session)

    assert message.uuid == return_uuid
    decrypt_fn.assert_not_called()
    download_fn.assert_not_called()


def test_MessageDownloadJob_message_already_downloaded(mocker, homedir, session, session_maker):
    """
    Test that call_api just decrypts and returns uuid if already downloaded.
    """
    message = factory.Message(source=factory.Source(), is_downloaded=True, is_decrypted=None)
    session.add(message)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = MessageDownloadJob(message.uuid, homedir, gpg)
    mocker.patch.object(job.gpg, 'decrypt_submission_or_reply')
    api_client = mocker.MagicMock()
    download_fn = mocker.patch.object(api_client, 'download_submission')

    return_uuid = job.call_api(api_client, session)

    assert message.uuid == return_uuid
    assert message.is_decrypted is True
    download_fn.assert_not_called()


def test_MessageDownloadJob_happiest_path(mocker, homedir, session, session_maker):
    """
    Test when a message successfully downloads and decrypts. Use the `homedir` fixture to get a GPG
    keyring.
    """
    message = factory.Message(
        source=factory.Source(), is_downloaded=False, is_decrypted=None, content=None)
    session.add(message)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = MessageDownloadJob(message.uuid, homedir, gpg)
    mocker.patch.object(job.gpg, 'decrypt_submission_or_reply')
    api_client = mocker.MagicMock()
    data_dir = os.path.join(homedir, 'data')
    api_client.download_submission = mocker.MagicMock(return_value=('', data_dir))

    job.call_api(api_client, session)

    assert message.content is not None
    assert message.is_downloaded is True
    assert message.is_decrypted is True


def test_MessageDownloadJob_with_crypto_error(mocker, homedir, session, session_maker):
    """
    Test when a message successfully downloads, but does not successfully decrypt. Use the `homedir`
    fixture to get a GPG keyring.
    """
    message = factory.Message(
        source=factory.Source(), is_downloaded=False, is_decrypted=None, content=None)
    session.add(message)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = MessageDownloadJob(message.uuid, homedir, gpg)
    mocker.patch.object(job.gpg, 'decrypt_submission_or_reply', side_effect=CryptoError)
    api_client = mocker.MagicMock()
    api_client = mocker.MagicMock()
    path = os.path.join(homedir, 'data')
    api_client.download_submission = mocker.MagicMock(return_value=('', path))

    job.call_api(api_client, session)

    assert message.content is None
    assert message.is_downloaded is True
    assert message.is_decrypted is False


def test_FileDownloadJob_message_already_decrypted(mocker, homedir, session, session_maker):
    """
    Test that call_api just returns uuid if already decrypted.
    """
    file = factory.File(source=factory.Source(), is_downloaded=True, is_decrypted=True)
    session.add(file)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = FileDownloadJob(db.File, file.uuid, homedir, gpg)
    decrypt_fn = mocker.patch.object(job.gpg, 'decrypt_submission_or_reply')
    api_client = mocker.MagicMock()
    download_fn = mocker.patch.object(api_client, 'download_submission')

    return_uuid = job.call_api(api_client, session)

    assert file.uuid == return_uuid
    decrypt_fn.assert_not_called()
    download_fn.assert_not_called()


def test_FileDownloadJob_message_already_downloaded(mocker, homedir, session, session_maker):
    """
    Test that call_api just decrypts and returns uuid if already downloaded.
    """
    file = factory.File(source=factory.Source(), is_downloaded=True, is_decrypted=False)
    session.add(file)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = FileDownloadJob(db.File, file.uuid, homedir, gpg)
    mocker.patch.object(job.gpg, 'decrypt_submission_or_reply')
    api_client = mocker.MagicMock()
    download_fn = mocker.patch.object(api_client, 'download_submission')

    return_uuid = job.call_api(api_client, session)

    assert file.uuid == return_uuid
    assert file.is_decrypted is True
    download_fn.assert_not_called()


def test_FileDownloadJob_happy_path_no_etag(mocker, homedir, session, session_maker):
    source = factory.Source()
    file_ = factory.File(source=source, is_downloaded=False, is_decrypted=None)
    session.add(source)
    session.add(file_)
    session.commit()

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    mock_decrypt = mocker.patch.object(gpg, 'decrypt_submission_or_reply')

    def fake_download(sdk_obj: sdclientapi.Submission) -> Tuple[str, str]:
        '''
        :return: (etag, path_to_dl)
        '''
        full_path = os.path.join(homedir, 'data', 'mock')
        with open(full_path, 'wb') as f:
            f.write(b'')
        return ('', full_path)

    api_client = mocker.MagicMock()
    api_client.download_submission = fake_download

    job = FileDownloadJob(
        db.File,
        file_.uuid,
        os.path.join(homedir, 'data'),
        gpg,
    )

    mock_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger')

    job.call_api(api_client, session)

    log_msg = mock_logger.debug.call_args_list[0][0][0]
    assert log_msg.startswith('No ETag. Skipping integrity check')

    # ensure mocks aren't stale
    assert mock_decrypt.called


def test_FileDownloadJob_happy_path_sha256_etag(mocker, homedir, session, session_maker):
    source = factory.Source()
    file_ = factory.File(source=source, is_downloaded=None, is_decrypted=None)
    session.add(source)
    session.add(file_)
    session.commit()

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    mock_decrypt = mocker.patch.object(gpg, 'decrypt_submission_or_reply')

    def fake_download(sdk_obj: sdclientapi.Submission) -> Tuple[str, str]:
        '''
        :return: (etag, path_to_dl)
        '''
        full_path = os.path.join(homedir, 'data', 'mock')
        with open(full_path, 'wb') as f:
            f.write(b'wat')

        # sha256 of b'wat'
        return ('sha256:f00a787f7492a95e165b470702f4fe9373583fbdc025b2c8bdf0262cc48fcff4',
                full_path)

    api_client = mocker.MagicMock()
    api_client.download_submission = fake_download

    job = FileDownloadJob(
        db.File,
        file_.uuid,
        os.path.join(homedir, 'data'),
        gpg,
    )

    job.call_api(api_client, session)

    # ensure mocks aren't stale
    assert mock_decrypt.called


def test_FileDownloadJob_bad_sha256_etag(mocker, homedir, session, session_maker):
    source = factory.Source()
    file_ = factory.File(source=source, is_downloaded=None, is_decrypted=None)
    session.add(source)
    session.add(file_)
    session.commit()

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)

    def fake_download(sdk_obj: sdclientapi.Submission) -> Tuple[str, str]:
        '''
        :return: (etag, path_to_dl)
        '''
        full_path = os.path.join(homedir, 'data', 'mock')
        with open(full_path, 'wb') as f:
            f.write(b'')

        return ('sha256:not-a-sha-sum',
                full_path)

    api_client = mocker.MagicMock()
    api_client.download_submission = fake_download

    job = FileDownloadJob(
        db.File,
        file_.uuid,
        os.path.join(homedir, 'data'),
        gpg,
    )

    # we currently don't handle errors in the checksum
    with pytest.raises(RuntimeError):
        job.call_api(api_client, session)


def test_FileDownloadJob_happy_path_unknown_etag(mocker, homedir, session, session_maker):
    source = factory.Source()
    file_ = factory.File(source=source, is_downloaded=None, is_decrypted=None)
    session.add(source)
    session.add(file_)
    session.commit()

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)

    def fake_download(sdk_obj: sdclientapi.Submission) -> Tuple[str, str]:
        '''
        :return: (etag, path_to_dl)
        '''
        full_path = os.path.join(homedir, 'data', 'mock')
        with open(full_path, 'wb') as f:
            f.write(b'')
        return ('UNKNOWN:abc123',
                full_path)

    api_client = mocker.MagicMock()
    api_client.download_submission = fake_download

    job = FileDownloadJob(
        db.File,
        file_.uuid,
        os.path.join(homedir, 'data'),
        gpg,
    )

    mock_decrypt = mocker.patch('securedrop_client.crypto.GpgHelper.decrypt_submission_or_reply')
    mock_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger')

    job.call_api(api_client, session)

    log_msg = mock_logger.debug.call_args_list[0][0][0]
    assert log_msg.startswith('Unknown hash algorithm')

    # ensure mocks aren't stale
    assert mock_decrypt.called


def test_FileDownloadJob_decryption_error(mocker, homedir, session, session_maker):
    source = factory.Source()
    file_ = factory.File(source=source, is_downloaded=None, is_decrypted=None)
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
        full_path = os.path.join(homedir, 'data', 'mock')
        with open(full_path, 'wb') as f:
            f.write(b'wat')

        # sha256 of b'wat'
        return ('sha256:f00a787f7492a95e165b470702f4fe9373583fbdc025b2c8bdf0262cc48fcff4',
                full_path)

    api_client = mocker.MagicMock()
    api_client.download_submission = fake_download

    job = FileDownloadJob(
        db.File,
        file_.uuid,
        os.path.join(homedir, 'data'),
        gpg,
    )

    mock_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger')

    with pytest.raises(CryptoError):
        job.call_api(api_client, session)

    log_msg = mock_logger.debug.call_args_list[0][0][0]
    assert log_msg.startswith('Failed to decrypt file')

    # ensure mocks aren't stale
    assert mock_decrypt.called
