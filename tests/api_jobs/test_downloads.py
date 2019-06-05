import os
import pytest
import sdclientapi
from typing import Tuple

from securedrop_client import db
from securedrop_client.api_jobs.downloads import FileDownloadJob
from securedrop_client.crypto import GpgHelper, CryptoError
from tests import factory


def test_FileDownloadJob_happy_path_no_etag(mocker, homedir, session, session_maker):
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

    job = FileDownloadJob(
        db.File,
        file_.uuid,
        homedir,
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

    job = FileDownloadJob(
        db.File,
        file_.uuid,
        homedir,
        gpg,
    )

    job.call_api(api_client, session)

    # ensure mocks aren't stale
    assert mock_decrypt.called


def test_FileDownloadJob_bad_sha256_etag(mocker, homedir, session, session_maker):
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

    job = FileDownloadJob(
        db.File,
        file_.uuid,
        homedir,
        gpg,
    )

    # we currently don't handle errors in the checksum
    with pytest.raises(RuntimeError):
        job.call_api(api_client, session)


def test_FileDownloadJob_happy_path_unknown_etag(mocker, homedir, session, session_maker):
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

    job = FileDownloadJob(
        db.File,
        file_.uuid,
        homedir,
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

    job = FileDownloadJob(
        db.File,
        file_.uuid,
        homedir,
        gpg,
    )

    mock_logger = mocker.patch('securedrop_client.api_jobs.downloads.logger')

    with pytest.raises(CryptoError):
        job.call_api(api_client, session)

    log_msg = mock_logger.debug.call_args_list[0][0][0]
    assert log_msg.startswith('Failed to decrypt file')

    # ensure mocks aren't stale
    assert mock_decrypt.called
