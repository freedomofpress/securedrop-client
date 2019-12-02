from unittest import mock

import os
import pytest
import subprocess  # noqa: F401
import sys
import tempfile
from subprocess import CalledProcessError

from securedrop_export import export

SAMPLE_OUTPUT_NO_PRINTER = b"network beh\nnetwork https\nnetwork ipp\nnetwork ipps\nnetwork http\nnetwork\nnetwork ipp14\nnetwork lpd"  # noqa
SAMPLE_OUTPUT_BROTHER_PRINTER = b"network beh\nnetwork https\nnetwork ipp\nnetwork ipps\nnetwork http\nnetwork\nnetwork ipp14\ndirect usb://Brother/HL-L2320D%20series?serial=A00000A000000\nnetwork lpd"  # noqa
SAMPLE_OUTPUT_LASERJET_PRINTER = b"network beh\nnetwork https\nnetwork ipp\nnetwork ipps\nnetwork http\nnetwork\nnetwork ipp14\ndirect usb://HP/LaserJet%20Pro%20M404-M405?serial=A00000A000000\nnetwork lpd"  # noqa

SAMPLE_OUTPUT_NO_PART = b"disk\ncrypt"  # noqa
SAMPLE_OUTPUT_ONE_PART = b"disk\npart\ncrypt"  # noqa
SAMPLE_OUTPUT_MULTI_PART = b"disk\npart\npart\npart\ncrypt"  # noqa
SAMPLE_OUTPUT_USB = b"/dev/sda"  # noqa
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


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_BROTHER_PRINTER)
def test_get_good_printer_uri_laserjet(mocked_call):
    submission = export.SDExport("testfile", TEST_CONFIG)

    result = submission.get_printer_uri()

    assert result == "usb://Brother/HL-L2320D%20series?serial=A00000A000000"


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_LASERJET_PRINTER)
def test_get_good_printer_uri_brother(mocked_call):
    submission = export.SDExport("testfile", TEST_CONFIG)
    result = submission.get_printer_uri()
    assert result == "usb://HP/LaserJet%20Pro%20M404-M405?serial=A00000A000000"


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_NO_PRINTER)
def test_get_bad_printer_uri(mocked_call, capsys, mocker):
    submission = export.SDExport("testfile", TEST_CONFIG)
    expected_message = "ERROR_PRINTER_NOT_FOUND"
    assert export.ExportStatus.ERROR_PRINTER_NOT_FOUND.value == expected_message
    mocked_exit = mocker.patch.object(submission, "exit_gracefully",
                                      side_effect=lambda x: sys.exit(0))

    with pytest.raises(SystemExit):
        submission.get_printer_uri()

    mocked_exit.assert_called_once_with(expected_message)


@pytest.mark.parametrize('open_office_paths', [
    "/tmp/whatver/thisisadoc.doc"
    "/home/user/Downloads/thisisadoc.xlsx"
    "/home/user/Downloads/file.odt"
    "/tmp/tmpJf83j9/secret.pptx"
])
def test_is_open_office_file(capsys, open_office_paths):
    submission = export.SDExport("", TEST_CONFIG)
    assert submission.is_open_office_file(open_office_paths)


@pytest.mark.parametrize('open_office_paths', [
    "/tmp/whatver/thisisadoc.doccc"
    "/home/user/Downloads/thisisa.xlsx.zip"
    "/home/user/Downloads/file.odz"
    "/tmp/tmpJf83j9/secret.gpg"
])
def test_is_not_open_office_file(capsys, open_office_paths):
    submission = export.SDExport("", TEST_CONFIG)
    assert not submission.is_open_office_file(open_office_paths)


def test_usb_precheck_disconnected(capsys, mocker):
    submission = export.SDExport("testfile", TEST_CONFIG)
    expected_message = "USB_NOT_CONNECTED"
    assert export.ExportStatus.USB_NOT_CONNECTED.value == expected_message
    mocked_exit = mocker.patch.object(submission, "exit_gracefully", return_value=0)

    mocker.patch("subprocess.check_output",
                 side_effect=CalledProcessError(1, 'check_output'))

    submission.check_usb_connected()
    mocked_exit.assert_called_once_with(expected_message)


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_USB)
def test_usb_precheck_connected(mocked_call, capsys, mocker):
    submission = export.SDExport("testfile", TEST_CONFIG)
    expected_message = "USB_CONNECTED"
    assert export.ExportStatus.USB_CONNECTED.value == expected_message
    mocked_exit = mocker.patch.object(submission, "exit_gracefully", return_value=0)

    submission.check_usb_connected()

    mocked_exit.assert_called_once_with(expected_message)


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_NO_PART)
def test_extract_device_name_no_part(mocked_call, capsys):
    submission = export.SDExport("testfile", TEST_CONFIG)

    submission.set_extracted_device_name()

    assert submission.device == "/dev/sda"


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_ONE_PART)
def test_extract_device_name_single_part(mocked_call, capsys):
    submission = export.SDExport("testfile", TEST_CONFIG)

    submission.set_extracted_device_name()

    assert submission.device == "/dev/sda1"


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_MULTI_PART)
def test_extract_device_name_multiple_part(mocked_call, capsys, mocker):
    submission = export.SDExport("testfile", TEST_CONFIG)
    mocked_exit = mocker.patch.object(submission, "exit_gracefully", return_value=0)
    expected_message = export.ExportStatus.USB_ENCRYPTION_NOT_SUPPORTED.value

    submission.set_extracted_device_name()

    mocked_exit.assert_called_once_with(expected_message)


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_NO_PART)
@mock.patch("subprocess.check_call", return_value=0)
def test_luks_precheck_encrypted_fde(mocked_call, capsys, mocker):
    submission = export.SDExport("testfile", TEST_CONFIG)
    expected_message = export.ExportStatus.USB_ENCRYPTED.value
    mocked_exit = mocker.patch.object(submission, "exit_gracefully", return_value=0)

    submission.check_luks_volume()

    mocked_exit.assert_called_once_with(expected_message)


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_ONE_PART)
@mock.patch("subprocess.check_call", return_value=0)
def test_luks_precheck_encrypted_single_part(mocked_call, capsys, mocker):
    submission = export.SDExport("testfile", TEST_CONFIG)
    expected_message = export.ExportStatus.USB_ENCRYPTED.value
    mocked_exit = mocker.patch.object(submission, "exit_gracefully", return_value=0)

    submission.check_luks_volume()

    mocked_exit.assert_called_once_with(expected_message)


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_MULTI_PART)
def test_luks_precheck_encrypted_multi_part(mocked_call, capsys, mocker):
    submission = export.SDExport("testfile", TEST_CONFIG)
    expected_message = export.ExportStatus.USB_ENCRYPTION_NOT_SUPPORTED.value

    # Here we need to mock the exit_gracefully method with a side effect otherwise
    # program execution will continue after exit_gracefully and exit_gracefully
    # may be called a second time.
    mocked_exit = mocker.patch.object(submission, "exit_gracefully",
                                      side_effect=lambda x: sys.exit(0))

    # Output of `lsblk -o TYPE --noheadings DEVICE_NAME` when a drive has multiple
    # partitions
    multi_partition_lsblk_output = b"disk\npart\npart\n"
    mocker.patch("subprocess.check_call", return_value=0)
    mocker.patch("subprocess.check_output", return_value=multi_partition_lsblk_output)

    with pytest.raises(SystemExit):
        submission.check_luks_volume()

    mocked_exit.assert_called_once_with(expected_message)


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_ONE_PART)
def test_luks_precheck_encrypted_luks_error(mocked_call, capsys, mocker):
    submission = export.SDExport("testfile", TEST_CONFIG)
    expected_message = "USB_ENCRYPTION_NOT_SUPPORTED"
    assert expected_message == export.ExportStatus.USB_ENCRYPTION_NOT_SUPPORTED.value

    mocked_exit = mocker.patch.object(submission, "exit_gracefully",
                                      side_effect=lambda msg, e: sys.exit(0))

    single_partition_lsblk_output = b"disk\npart\n"
    mocker.patch("subprocess.check_output", return_value=single_partition_lsblk_output)
    mocker.patch("subprocess.check_call", side_effect=CalledProcessError(1, 'check_call'))

    with pytest.raises(SystemExit):
        submission.check_luks_volume()

    assert mocked_exit.mock_calls[0][2]['msg'] == expected_message
    assert mocked_exit.mock_calls[0][2]['e'] is None


def test_safe_check_call(capsys, mocker):
    submission = export.SDExport("testfile", TEST_CONFIG)
    submission.safe_check_call(['ls'], "this will work")
    mocked_exit = mocker.patch.object(submission, "exit_gracefully", return_value=0)
    expected_message = "uh oh!!!!"

    submission.safe_check_call(['ls', 'kjdsfhkdjfh'], expected_message)

    assert mocked_exit.mock_calls[0][2]['msg'] == expected_message
    assert mocked_exit.mock_calls[0][2]['e'] is None
