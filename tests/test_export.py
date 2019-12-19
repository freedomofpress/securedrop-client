from unittest import mock

import os
import pytest
import subprocess  # noqa: F401
import tempfile

from securedrop_export import export

TEST_CONFIG = os.path.join(os.path.dirname(__file__), "sd-export-config.json")
BAD_TEST_CONFIG = os.path.join(os.path.dirname(__file__), "sd-export-config-bad.json")
ANOTHER_BAD_TEST_CONFIG = os.path.join(os.path.dirname(__file__), "sd-export-config-bad-2.json")


def test_exit_gracefully_no_exception(capsys):

    submission = export.SDExport("testfile", TEST_CONFIG)
    test_msg = 'test'

    with pytest.raises(SystemExit) as sysexit:
        submission.exit_gracefully(test_msg)

    # A graceful exit means a return code of 0
    assert sysexit.value.code == 0

    captured = capsys.readouterr()
    assert captured.err == "{}\n".format(test_msg)
    assert captured.out == ""


def test_exit_gracefully_exception(capsys):
    submission = export.SDExport("testfile", TEST_CONFIG)
    test_msg = 'test'

    with pytest.raises(SystemExit) as sysexit:
        submission.exit_gracefully(
            test_msg, e=Exception('BANG!')
        )

    # A graceful exit means a return code of 0
    assert sysexit.value.code == 0

    captured = capsys.readouterr()
    assert captured.err == export.ExportStatus.ERROR_GENERIC.value
    assert captured.out == ""


def test_empty_config(capsys):
    export.SDExport("testfile", TEST_CONFIG)
    temp_folder = tempfile.mkdtemp()
    metadata = os.path.join(temp_folder, export.Metadata.METADATA_FILE)
    with open(metadata, "w") as f:
        f.write("{}")

    config = export.Metadata(temp_folder)

    assert not config.is_valid()


def test_valid_printer_test_config(capsys):
    export.SDExport("testfile", TEST_CONFIG)
    temp_folder = tempfile.mkdtemp()
    metadata = os.path.join(temp_folder, export.Metadata.METADATA_FILE)
    with open(metadata, "w") as f:
        f.write('{"device": "printer-test"}')

    config = export.Metadata(temp_folder)

    assert config.is_valid()
    assert config.encryption_key is None
    assert config.encryption_method is None


def test_valid_printer_config(capsys):
    export.SDExport("", TEST_CONFIG)
    temp_folder = tempfile.mkdtemp()
    metadata = os.path.join(temp_folder, export.Metadata.METADATA_FILE)
    with open(metadata, "w") as f:
        f.write('{"device": "printer"}')

    config = export.Metadata(temp_folder)

    assert config.is_valid()
    assert config.encryption_key is None
    assert config.encryption_method is None


def test_invalid_encryption_config(capsys):
    export.SDExport("testfile", TEST_CONFIG)

    temp_folder = tempfile.mkdtemp()
    metadata = os.path.join(temp_folder, export.Metadata.METADATA_FILE)
    with open(metadata, "w") as f:
        f.write(
            '{"device": "disk", "encryption_method": "base64", "encryption_key": "hunter1"}'
        )

    config = export.Metadata(temp_folder)

    assert config.encryption_key == "hunter1"
    assert config.encryption_method == "base64"
    assert not config.is_valid()


def test_valid_encryption_config(capsys):
    export.SDExport("testfile", TEST_CONFIG)
    temp_folder = tempfile.mkdtemp()
    metadata = os.path.join(temp_folder, export.Metadata.METADATA_FILE)
    with open(metadata, "w") as f:
        f.write(
            '{"device": "disk", "encryption_method": "luks", "encryption_key": "hunter1"}'
        )

    config = export.Metadata(temp_folder)

    assert config.encryption_key == "hunter1"
    assert config.encryption_method == "luks"
    assert config.is_valid()


@mock.patch("subprocess.check_call")
def test_popup_message(mocked_call):
    submission = export.SDExport("testfile", TEST_CONFIG)
    submission.popup_message("hello!")
    mocked_call.assert_called_once_with([
        "notify-send",
        "--expire-time", "3000",
        "--icon", "/usr/share/securedrop/icons/sd-logo.png",
        "SecureDrop: hello!"
    ])


def test_safe_check_call(capsys, mocker):
    submission = export.SDExport("testfile", TEST_CONFIG)
    submission.safe_check_call(['ls'], "this will work")
    mocked_exit = mocker.patch.object(submission, "exit_gracefully", return_value=0)
    expected_message = "uh oh!!!!"

    submission.safe_check_call(['ls', 'kjdsfhkdjfh'], expected_message)

    assert mocked_exit.mock_calls[0][2]['msg'] == expected_message
    assert mocked_exit.mock_calls[0][2]['e'] is None
