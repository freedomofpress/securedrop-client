import os
import pytest
from typing import Tuple

from sdclientapi import BaseError
from sdclientapi import Submission as SdkSubmission

from securedrop_client.api_jobs.downloads import DownloadJob, FileDownloadJob, MessageDownloadJob, \
    ReplyDownloadJob, DownloadChecksumMismatchException, MetadataSyncJob
from securedrop_client.crypto import GpgHelper, CryptoError
from tests import factory

with open(os.path.join(os.path.dirname(__file__), '..', 'files', 'test-key.gpg.pub.asc')) as f:
    PUB_KEY = f.read()


def patch_decrypt(mocker, homedir, gpghelper, filename):
    mock_decrypt = mocker.patch.object(gpghelper, 'decrypt_submission_or_reply')
    fn_no_ext, _ = os.path.splitext(os.path.splitext(os.path.basename(filename))[0])
    mock_decrypt.return_value = fn_no_ext
    return mock_decrypt


def test_MetadataSyncJob_success(mocker, homedir, session, session_maker):
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = MetadataSyncJob(homedir, gpg)

    mock_source = mocker.MagicMock()
    mock_source.uuid = 'bar'
    mock_source.key = {
        'type': 'PGP',
        'public': PUB_KEY,
        'fingerprint': '123456ABC',
    }

    mock_key_import = mocker.patch.object(job.gpg, 'import_key')
    mock_get_remote_data = mocker.patch(
        'securedrop_client.api_jobs.downloads.get_remote_data',
        return_value=([mock_source], 'submissions', 'replies'))

    api_client = 'foo'

    mocker.patch(
        'securedrop_client.api_jobs.downloads.update_local_storage',
        return_value=([mock_source], 'submissions', 'replies'))

    job.call_api(api_client, session)

    assert mock_key_import.call_args[0][0] == mock_source.uuid
    assert mock_key_import.call_args[0][1] == mock_source.key['public']
    assert mock_key_import.call_args[0][2] == mock_source.key['fingerprint']
    assert mock_get_remote_data.call_count == 1


def test_MetadataSyncJob_success_with_key_import_fail(mocker, homedir, session, session_maker):
    """
    Check that we can gracefully handle a key import failure.
    """
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = MetadataSyncJob(homedir, gpg)

    mock_source = mocker.MagicMock()
    mock_source.uuid = 'bar'
    mock_source.key = {
        'type': 'PGP',
        'public': PUB_KEY,
        'fingerprint': '123456ABC',
    }

    mock_key_import = mocker.patch.object(job.gpg, 'import_key',
                                          side_effect=CryptoError)
    mock_get_remote_data = mocker.patch(
        'securedrop_client.api_jobs.downloads.get_remote_data',
        return_value=([mock_source], 'submissions', 'replies'))

    api_client = 'foo'

    mocker.patch(
        'securedrop_client.api_jobs.downloads.update_local_storage',
        return_value=([mock_source], 'submissions', 'replies'))

    job.call_api(api_client, session)

    assert mock_key_import.call_args[0][0] == mock_source.uuid
    assert mock_key_import.call_args[0][1] == mock_source.key['public']
    assert mock_key_import.call_args[0][2] == mock_source.key['fingerprint']
    assert mock_get_remote_data.call_count == 1


def test_MetadataSyncJob_success_with_missing_key(mocker, homedir, session, session_maker):
    """
    Check that we can gracefully handle missing source keys.
    """
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = MetadataSyncJob(homedir, gpg)

    mock_source = mocker.MagicMock()
    mock_source.uuid = 'bar'
    mock_source.key = {
        'type': 'PGP',
        'pub_key': '',
        'fingerprint': ''
    }

    mock_key_import = mocker.patch.object(job.gpg, 'import_key')
    mock_get_remote_data = mocker.patch(
        'securedrop_client.api_jobs.downloads.get_remote_data',
        return_value=([mock_source], 'submissions', 'replies'))

    api_client = 'foo'

    mocker.patch(
        'securedrop_client.api_jobs.downloads.update_local_storage',
        return_value=([mock_source], 'submissions', 'replies'))

    job.call_api(api_client, session)

    assert mock_key_import.call_count == 0
    assert mock_get_remote_data.call_count == 1


def test_MessageDownloadJob_raises_NotImplementedError(mocker):
    job = DownloadJob('mock')

    with pytest.raises(NotImplementedError):
        job.call_download_api(None, None)

    with pytest.raises(NotImplementedError):
        job.call_decrypt(None, None)

    with pytest.raises(NotImplementedError):
        job.get_db_object(None)


def test_ReplyDownloadJob_no_download_or_decrypt(mocker, homedir, session, session_maker):
    """
    Test that an already-downloaded reply successfully decrypts.
    """
    reply_is_decrypted_false = factory.Reply(
        source=factory.Source(), is_downloaded=True, is_decrypted=False, content=None)
    reply_is_decrypted_none = factory.Reply(
        source=factory.Source(), is_downloaded=True, is_decrypted=None, content=None)
    session.add(reply_is_decrypted_false)
    session.add(reply_is_decrypted_none)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job_1 = ReplyDownloadJob(reply_is_decrypted_false.uuid, homedir, gpg)
    job_2 = ReplyDownloadJob(reply_is_decrypted_none.uuid, homedir, gpg)
    mocker.patch.object(job_1.gpg, 'decrypt_submission_or_reply')
    mocker.patch.object(job_2.gpg, 'decrypt_submission_or_reply')
    api_client = mocker.MagicMock()
    path = os.path.join(homedir, 'data')
    api_client.download_submission = mocker.MagicMock(return_value=('', path))

    job_1.call_api(api_client, session)
    job_2.call_api(api_client, session)

    assert reply_is_decrypted_false.content is not None
    assert reply_is_decrypted_false.is_downloaded is True
    assert reply_is_decrypted_false.is_decrypted is True
    assert reply_is_decrypted_none.content is not None
    assert reply_is_decrypted_none.is_downloaded is True
    assert reply_is_decrypted_none.is_decrypted is True


def test_ReplyDownloadJob_message_already_decrypted(mocker, homedir, session, session_maker):
    """
    Test that call_api just returns uuid if already decrypted.
    """
    reply = factory.Reply(source=factory.Source(), is_downloaded=True, is_decrypted=True)
    session.add(reply)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = ReplyDownloadJob(reply.uuid, homedir, gpg)
    decrypt_fn = mocker.patch.object(job.gpg, 'decrypt_submission_or_reply')
    api_client = mocker.MagicMock()
    download_fn = mocker.patch.object(api_client, 'download_reply')

    return_uuid = job.call_api(api_client, session)

    assert reply.uuid == return_uuid
    decrypt_fn.assert_not_called()
    download_fn.assert_not_called()


def test_ReplyDownloadJob_message_already_downloaded(mocker, homedir, session, session_maker):
    """
    Test that call_api just decrypts and returns uuid if already downloaded.
    """
    reply = factory.Reply(source=factory.Source(), is_downloaded=True, is_decrypted=None)
    session.add(reply)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = ReplyDownloadJob(reply.uuid, homedir, gpg)
    mocker.patch.object(job.gpg, 'decrypt_submission_or_reply')
    api_client = mocker.MagicMock()
    download_fn = mocker.patch.object(api_client, 'download_reply')

    return_uuid = job.call_api(api_client, session)

    assert reply.uuid == return_uuid
    assert reply.is_decrypted is True
    download_fn.assert_not_called()


def test_ReplyDownloadJob_happiest_path(mocker, homedir, session, session_maker):
    """
    Test when a reply successfully downloads and decrypts. Use the `homedir` fixture to get a GPG
    keyring.
    """
    reply = factory.Reply(
        source=factory.Source(), is_downloaded=False, is_decrypted=None, content=None)
    session.add(reply)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = ReplyDownloadJob(reply.uuid, homedir, gpg)
    mocker.patch.object(job.gpg, 'decrypt_submission_or_reply')
    api_client = mocker.MagicMock()
    data_dir = os.path.join(homedir, 'data')
    api_client.download_reply = mocker.MagicMock(return_value=('', data_dir))

    job.call_api(api_client, session)

    assert reply.content is not None
    assert reply.is_downloaded is True
    assert reply.is_decrypted is True


def test_MessageDownloadJob_no_download_or_decrypt(mocker, homedir, session, session_maker):
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


def test_MessageDownloadJob_with_base_error(mocker, homedir, session, session_maker):
    """
    Test when a message does not successfully download.
    """
    message = factory.Message(
        source=factory.Source(), is_downloaded=False, is_decrypted=None, content=None)
    session.add(message)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = MessageDownloadJob(message.uuid, homedir, gpg)
    api_client = mocker.MagicMock()
    mocker.patch.object(api_client, 'download_submission', side_effect=BaseError)
    decrypt_fn = mocker.patch.object(job.gpg, 'decrypt_submission_or_reply')

    with pytest.raises(BaseError):
        job.call_api(api_client, session)

    assert message.content is None
    assert message.is_downloaded is False
    assert message.is_decrypted is None
    decrypt_fn.assert_not_called()


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

    with pytest.raises(CryptoError):
        job.call_api(api_client, session)

    assert message.content is None
    assert message.is_downloaded is True
    assert message.is_decrypted is False


def test_FileDownloadJob_message_already_decrypted(mocker, homedir, session, session_maker):
    """
    Test that call_api just returns uuid if already decrypted.
    """
    file_ = factory.File(source=factory.Source(), is_downloaded=True, is_decrypted=True)
    session.add(file_)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = FileDownloadJob(file_.uuid, homedir, gpg)
    decrypt_fn = mocker.patch.object(job.gpg, 'decrypt_submission_or_reply')
    api_client = mocker.MagicMock()
    download_fn = mocker.patch.object(api_client, 'download_submission')

    return_uuid = job.call_api(api_client, session)

    assert file_.uuid == return_uuid
    decrypt_fn.assert_not_called()
    download_fn.assert_not_called()


def test_FileDownloadJob_message_already_downloaded(mocker, homedir, session, session_maker):
    """
    Test that call_api just decrypts and returns uuid if already downloaded.
    """
    file_ = factory.File(source=factory.Source(), is_downloaded=True, is_decrypted=False)
    session.add(file_)
    session.commit()
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    job = FileDownloadJob(file_.uuid, os.path.join(homedir, 'data'), gpg)
    patch_decrypt(mocker, homedir, gpg, file_.filename)
    api_client = mocker.MagicMock()
    download_fn = mocker.patch.object(api_client, 'download_submission')

    return_uuid = job.call_api(api_client, session)

    assert file_.uuid == return_uuid
    assert file_.is_decrypted is True
    download_fn.assert_not_called()


def test_FileDownloadJob_happy_path_no_etag(mocker, homedir, session, session_maker):
    source = factory.Source()
    file_ = factory.File(source=source, is_downloaded=False, is_decrypted=None)
    session.add(source)
    session.add(file_)
    session.commit()

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    mock_decrypt = patch_decrypt(mocker, homedir, gpg, file_.filename)

    def fake_download(sdk_obj: SdkSubmission, timeout: int) -> Tuple[str, str]:
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
    mock_decrypt = patch_decrypt(mocker, homedir, gpg, file_.filename)

    def fake_download(sdk_obj: SdkSubmission, timeout: int) -> Tuple[str, str]:
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

    def fake_download(sdk_obj: SdkSubmission, timeout: int) -> Tuple[str, str]:
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
        file_.uuid,
        os.path.join(homedir, 'data'),
        gpg,
    )

    with pytest.raises(DownloadChecksumMismatchException):
        job.call_api(api_client, session)


def test_FileDownloadJob_happy_path_unknown_etag(mocker, homedir, session, session_maker):
    source = factory.Source()
    file_ = factory.File(source=source, is_downloaded=None, is_decrypted=None)
    session.add(source)
    session.add(file_)
    session.commit()

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)

    def fake_download(sdk_obj: SdkSubmission, timeout: int) -> Tuple[str, str]:
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
        file_.uuid,
        os.path.join(homedir, 'data'),
        gpg,
    )

    mock_decrypt = patch_decrypt(mocker, homedir, gpg, file_.filename)
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
    mock_decrypt = mocker.patch.object(gpg, 'decrypt_submission_or_reply', side_effect=CryptoError)

    def fake_download(sdk_obj: SdkSubmission, timeout: int) -> Tuple[str, str]:
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


def test_timeout_length_of_file_downloads(mocker, homedir, session, session_maker):
    """
    Ensure that files downloads have timeouts scaled by the size of the file.
    """
    source = factory.Source()
    zero_byte_file = factory.File(source=source, is_downloaded=None, is_decrypted=None, size=0)
    one_byte_file = factory.File(source=source, is_downloaded=None, is_decrypted=None, size=1)
    KB_file = factory.File(source=source, is_downloaded=None, is_decrypted=None, size=1000)
    fifty_KB_file = factory.File(source=source, is_downloaded=None, is_decrypted=None, size=50000)
    half_MB_file = factory.File(source=source, is_downloaded=None, is_decrypted=None, size=500000)
    MB_file = factory.File(source=source, is_downloaded=None, is_decrypted=None, size=1000000)
    five_MB_file = factory.File(source=source, is_downloaded=None, is_decrypted=None, size=5000000)
    haf_GB_file = factory.File(source=source, is_downloaded=None, is_decrypted=None, size=500000000)
    GB_file = factory.File(source=source, is_downloaded=None, is_decrypted=None, size=1000000000)
    session.add(source)
    session.add(zero_byte_file)
    session.add(one_byte_file)
    session.add(KB_file)
    session.add(fifty_KB_file)
    session.add(half_MB_file)
    session.add(MB_file)
    session.add(five_MB_file)
    session.add(haf_GB_file)
    session.add(GB_file)
    session.commit()

    gpg = GpgHelper(homedir, session_maker, is_qubes=False)
    zero_byte_file_job = FileDownloadJob(zero_byte_file.uuid, os.path.join(homedir, 'data'), gpg)
    one_byte_file_job = FileDownloadJob(one_byte_file.uuid, os.path.join(homedir, 'data'), gpg)
    KB_file_job = FileDownloadJob(KB_file.uuid, os.path.join(homedir, 'data'), gpg)
    fifty_KB_file_job = FileDownloadJob(fifty_KB_file.uuid, os.path.join(homedir, 'data'), gpg)
    half_MB_file_job = FileDownloadJob(half_MB_file.uuid, os.path.join(homedir, 'data'), gpg)
    MB_file_job = FileDownloadJob(MB_file.uuid, os.path.join(homedir, 'data'), gpg)
    five_MB_file_job = FileDownloadJob(five_MB_file.uuid, os.path.join(homedir, 'data'), gpg)
    half_GB_file_job = FileDownloadJob(haf_GB_file.uuid, os.path.join(homedir, 'data'), gpg)
    GB_file_job = FileDownloadJob(GB_file.uuid, os.path.join(homedir, 'data'), gpg)

    zero_byte_file_timeout = zero_byte_file_job._get_realistic_timeout(zero_byte_file.size)
    one_byte_file_timeout = one_byte_file_job._get_realistic_timeout(one_byte_file.size)
    KB_file_timeout = KB_file_job._get_realistic_timeout(KB_file.size)
    fifty_KB_file_timeout = fifty_KB_file_job._get_realistic_timeout(fifty_KB_file.size)
    half_MB_file_timeout = half_MB_file_job._get_realistic_timeout(half_MB_file.size)
    MB_file_timeout = MB_file_job._get_realistic_timeout(MB_file.size)
    five_MB_file_timeout = five_MB_file_job._get_realistic_timeout(five_MB_file.size)
    GB_file_timeout = GB_file_job._get_realistic_timeout(GB_file.size)
    half_GB_file_timeout = half_GB_file_job._get_realistic_timeout(haf_GB_file.size)

    # timeout = ceil((file_size/100000)*1.5)+25
    assert zero_byte_file_timeout == 25
    assert one_byte_file_timeout == 26
    assert KB_file_timeout == 26
    assert fifty_KB_file_timeout == 26
    assert half_MB_file_timeout == 33
    assert MB_file_timeout == 40
    assert five_MB_file_timeout == 100
    assert half_GB_file_timeout == 7525
    assert GB_file_timeout == 15025
