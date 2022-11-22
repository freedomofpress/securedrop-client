import os
import struct
import subprocess
import tempfile

import pytest

from securedrop_client.crypto import CryptoError, GpgHelper, read_gzip_header_filename
from tests import factory

with open(os.path.join(os.path.dirname(__file__), "files", "test-key.gpg.pub.asc")) as f:
    PUB_KEY = f.read()

with open(os.path.join(os.path.dirname(__file__), "files", "securedrop.gpg.asc")) as f:
    JOURNO_KEY = f.read()


def test_message_logic(homedir, config, mocker, session_maker):
    """
    Ensure that messages are handled.
    Using the `config` fixture to ensure the config is written to disk.
    """
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)

    test_msg = "tests/files/test-msg.gpg"
    expected_output_filepath = os.path.join(homedir, "data", "test-msg")

    mock_gpg = mocker.patch("subprocess.call", return_value=0)
    mocker.patch("os.unlink")

    original_filename = gpg.decrypt_submission_or_reply(
        test_msg, expected_output_filepath, is_doc=False
    )

    assert mock_gpg.call_count == 1
    assert original_filename == "test-msg"


def test_gunzip_logic(homedir, config, mocker, session_maker):
    """
    Ensure that gzipped documents/files are handled
    Using the `config` fixture to ensure the config is written to disk.
    """
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)

    gpg._import(PUB_KEY)
    gpg._import(JOURNO_KEY)

    test_gzip = "tests/files/test-doc.gz.gpg"
    expected_output_filepath = "tests/files/test-doc.txt"

    # mock_gpg = mocker.patch('subprocess.call', return_value=0)
    mock_unlink = mocker.patch("os.unlink")
    original_filename = gpg.decrypt_submission_or_reply(
        test_gzip, expected_output_filepath, is_doc=True
    )

    assert original_filename == "test-doc.txt"

    # We should remove two files in the success scenario: err, filepath
    assert mock_unlink.call_count == 2
    mock_unlink.stop()
    os.remove(expected_output_filepath)


def test_gzip_header_without_filename(homedir, config, mocker, session_maker):
    """
    Test processing of a gzipped file without a filename in the header.
    """
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)

    gpg._import(PUB_KEY)
    gpg._import(JOURNO_KEY)

    mocker.patch("os.unlink")

    # pretend the gzipped file header lacked the original filename
    mock_read_gzip_header_filename = mocker.patch(
        "securedrop_client.crypto.read_gzip_header_filename"
    )
    mock_read_gzip_header_filename.return_value = ""

    test_gzip = "tests/files/test-doc.gz.gpg"
    output_filename = "test-doc"
    expected_output_filename = "tests/files/test-doc"

    original_filename = gpg.decrypt_submission_or_reply(test_gzip, output_filename, is_doc=True)
    assert original_filename == output_filename
    os.remove(expected_output_filename)


def test_read_gzip_header_filename_with_bad_file(homedir):
    with tempfile.NamedTemporaryFile() as tf:
        tf.write(b"test")
        tf.seek(0)
        with pytest.raises(OSError, match=r"Not a gzipped file"):
            read_gzip_header_filename(tf.name)


def test_read_gzip_header_filename_with_bad_compression_method(homedir):
    # 9 is a bad method
    header = struct.pack("<BBBBIxxHBBcccc", 31, 139, 9, 12, 0, 2, 1, 1, b"a", b"b", b"c", b"\0")
    with tempfile.NamedTemporaryFile() as tf:
        tf.write(header)
        tf.seek(0)
        with pytest.raises(OSError, match=r"Unknown compression method"):
            read_gzip_header_filename(tf.name)


def test_read_gzip_header_filename(homedir):
    header = struct.pack("<BBBBIxxHBBcccc", 31, 139, 8, 12, 0, 2, 1, 1, b"a", b"b", b"c", b"\0")
    with tempfile.NamedTemporaryFile() as tf:
        tf.write(header)
        tf.seek(0)
        assert "abc" == read_gzip_header_filename(tf.name)


def test_subprocess_raises_exception(homedir, config, mocker, session_maker):
    """
    Ensure that failed GPG commands raise an exception.
    Using the `config` fixture to ensure the config is written to disk.
    """
    gpg = GpgHelper(homedir, session_maker, is_qubes=False)

    test_gzip = "tests/files/test-doc.gz.gpg"
    output_filename = "test-doc"

    mock_gpg = mocker.patch("subprocess.call", return_value=1)
    mock_unlink = mocker.patch("os.unlink")

    with pytest.raises(CryptoError):
        gpg.decrypt_submission_or_reply(test_gzip, output_filename, is_doc=True)

    assert mock_gpg.call_count == 1
    # We should only remove one file in the failure scenario: err
    assert mock_unlink.call_count == 1


def test_import_key(homedir, config, session_maker):
    """
    Check the happy path that we can import a single PGP key.
    Using the `config` fixture to ensure the config is written to disk.
    """
    source = factory.Source()
    helper = GpgHelper(homedir, session_maker, is_qubes=False)
    helper.import_key(source)


def test_import_nonexistent_key(homedir, config, session_maker):
    """
    Check failure handling when a source has no key.
    """
    source = factory.Source(public_key=None)
    helper = GpgHelper(homedir, session_maker, is_qubes=False)
    with pytest.raises(CryptoError):
        helper.import_key(source)


def test_import_key_gpg_call_fail(homedir, config, mocker, session_maker):
    """
    Check that a `CryptoError` is raised if calling `gpg` fails.
    Using the `config` fixture to ensure the config is written to disk.
    """
    helper = GpgHelper(homedir, session_maker, is_qubes=False)
    source = factory.Source()
    err = subprocess.CalledProcessError(cmd=["foo"], returncode=1)
    mock_call = mocker.patch("securedrop_client.crypto.subprocess.check_call", side_effect=err)

    with pytest.raises(CryptoError, match="Could not import key."):
        helper.import_key(source)

    # ensure the mock was used
    assert mock_call.called


def test_encrypt(homedir, source, config, mocker, session_maker):
    """
    Check that calling `encrypt` encrypts the message.
    Using the `config` fixture to ensure the config is written to disk.
    """
    helper = GpgHelper(homedir, session_maker, is_qubes=False)

    # first we have to ensure the pubkeys are available
    helper._import(PUB_KEY)
    helper._import(JOURNO_KEY)

    plaintext = "bueller?"
    ciphertext = helper.encrypt_to_source(source["uuid"], plaintext)

    # check that we go *any* output just for sanity
    assert ciphertext

    ciphertext_file = os.path.join(homedir, "ciphertext.out")
    decrypted_file = os.path.join(homedir, "decrypted.out")
    gpg_home = os.path.join(homedir, "gpg")

    with open(ciphertext_file, "w") as f:
        f.write(ciphertext)

    subprocess.check_call(
        ["gpg", "--homedir", gpg_home, "--output", decrypted_file, "--decrypt", ciphertext_file]
    )

    with open(decrypted_file) as f:
        decrypted = f.read()

    assert decrypted == plaintext


def test_encrypt_fail(homedir, config, mocker, session_maker, session):
    """
    Check that a `CryptoError` is raised if the call to `gpg` fails.
    Using the `config` fixture to ensure the config is written to disk.
    """
    helper = GpgHelper(homedir, session_maker, is_qubes=False)

    source = factory.Source(public_key="iwillbreakyou")
    session.add(source)

    plaintext = "bueller?"

    # skip the import in encrypt_to_source, so encryption will fail
    helper.import_key = mocker.MagicMock(return_value=None)

    with pytest.raises(CryptoError):
        helper.encrypt_to_source(source.uuid, plaintext)

    assert helper.import_key.call_count == 1


def test_encrypt_fail_if_source_key_missing(homedir, config, mocker, session_maker, session):
    """
    Check that a `CryptoError` is raised before making a call to `gpg` if source key is
    missing.
    """
    helper = GpgHelper(homedir, session_maker, is_qubes=False)

    source = factory.Source(public_key=None)
    session.add(source)
    session.commit()

    check_call_fn = mocker.patch("securedrop_client.crypto.subprocess.check_call")

    with pytest.raises(
        CryptoError, match=f"Could not encrypt reply: no key for source {source.uuid}"
    ):
        helper.encrypt_to_source(source.uuid, "mock")

    check_call_fn.assert_not_called()


def test_encrypt_fail_if_journo_fingerprint_missing(homedir, source, config, mocker, session_maker):
    """
    Check that a `CryptoError` is raised before making a call to `gpg` if source fingerprint is
    missing.
    """
    helper = GpgHelper(homedir, session_maker, is_qubes=False)
    helper.journalist_key_fingerprint = None
    check_call_fn = mocker.patch("securedrop_client.crypto.subprocess.check_call")

    with pytest.raises(
        CryptoError, match=r"Could not encrypt reply due to missing fingerprint for journalist"
    ):
        helper.encrypt_to_source(source["uuid"], "mock")

    check_call_fn.assert_not_called()


def test_import_key_failure_in_encrypt_to_source(homedir, config, mocker, session_maker, session):
    """
    Confirm handling of key import failure.
    """
    helper = GpgHelper(homedir, session_maker, is_qubes=False)

    source = factory.Source(public_key="iwillbreakyou")
    session.add(source)

    plaintext = "bueller?"

    with pytest.raises(CryptoError, match=r"Could not import key before encrypting reply:"):
        helper.encrypt_to_source(source.uuid, plaintext)
