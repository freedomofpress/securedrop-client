from unittest import mock

import os
import pytest
import subprocess
import tempfile

from securedrop_export import export 

SAMPLE_OUTPUT_NO_PRINTER = b"network beh\nnetwork https\nnetwork ipp\nnetwork ipps\nnetwork http\nnetwork\nnetwork ipp14\nnetwork lpd"  # noqa
SAMPLE_OUTPUT_BOTHER_PRINTER = b"network beh\nnetwork https\nnetwork ipp\nnetwork ipps\nnetwork http\nnetwork\nnetwork ipp14\ndirect usb://Brother/HL-L2320D%20series?serial=A00000A000000\nnetwork lpd"  # noqa

SAMPLE_OUTPUT_NO_USB="Bus 001 Device 001: ID 1d6b:0002 Linux Foundation 2.0 root hub"  # noqa
SAMPLE_OUTPUT_USB="Bus 001 Device 002: ID 0781:5575 SanDisk Corp.\nBus 001 Device 001: ID 1d6b:0002 Linux Foundation 2.0 root hub"  # noqa
SAMPLE_OUTPUT_USB_ERROR=""
SAMPLE_OUTPUT_USB_ERROR2="h\ne\nl\nl\no"


def test_exit_gracefully_no_exception(capsys):
    submission = export.SDExport("testfile")
    test_msg = 'test'

    with pytest.raises(SystemExit) as sysexit:
        submission.exit_gracefully(test_msg)

    # A graceful exit means a return code of 0
    assert sysexit.value.code == 0

    captured = capsys.readouterr()
    assert captured.err == "{}\n".format(test_msg)
    assert captured.out == ""


def test_exit_gracefully_exception(capsys):
    submission = export.SDExport("testfile")
    test_msg = 'test'

    with pytest.raises(SystemExit) as sysexit:
        submission.exit_gracefully(test_msg,
                                         e=Exception('BANG!'))

    # A graceful exit means a return code of 0
    assert sysexit.value.code == 0

    captured = capsys.readouterr()
    assert captured.err == "{}\n<unknown exception>\n".format(test_msg)
    assert captured.out == ""


def test_empty_config(capsys):
    submission = export.SDExport("testfile")
    temp_folder = tempfile.mkdtemp()
    metadata = os.path.join(temp_folder, export.Metadata.METADATA_FILE)
    with open(metadata, "w") as f:
        f.write("{}")
    config = export.Metadata(temp_folder)
    assert not config.is_valid()


def test_valid_printer_test_config(capsys):
    submission = export.SDExport("testfile")
    temp_folder = tempfile.mkdtemp()
    metadata = os.path.join(temp_folder, export.Metadata.METADATA_FILE)
    with open(metadata, "w") as f:
        f.write('{"device": "printer-test"}')
    config = export.Metadata(temp_folder)
    assert config.is_valid()
    assert config.encryption_key is None
    assert config.encryption_method is None


def test_valid_printer_config(capsys):
    submission = export.SDExport("")
    temp_folder = tempfile.mkdtemp()
    metadata = os.path.join(temp_folder, export.Metadata.METADATA_FILE)
    with open(metadata, "w") as f:
        f.write('{"device": "printer"}')
    config = export.Metadata(temp_folder)
    assert config.is_valid()
    assert config.encryption_key is None
    assert config.encryption_method is None


def test_invalid_encryption_config(capsys):
    submission = export.SDExport("testfile")

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
    submission = export.SDExport("testfile")
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
    submission = export.SDExport("testfile")
    submission.popup_message("hello!")
    mocked_call.assert_called_once_with([
        "notify-send",
        "--expire-time", "3000",
        "--icon", "/usr/share/securedrop/icons/sd-logo.png",
        "SecureDrop: hello!"
    ])


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_BOTHER_PRINTER)
def test_get_good_printer_uri(mocked_call):
    submission = export.SDExport("testfile")
    result = submission.get_printer_uri()
    assert result == "usb://Brother/HL-L2320D%20series?serial=A00000A000000"


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_NO_PRINTER)
def test_get_bad_printer_uri(mocked_call, capsys):
    submission = export.SDExport("testfile")
    expected_message = "USB Printer not found"
    mocked_exit = mock.patch("export.exit_gracefully", return_value=0)

    with pytest.raises(SystemExit) as sysexit:
        result = submission.get_printer_uri()
        assert result == ""
        mocked_exit.assert_called_once_with(expected_message)

    assert sysexit.value.code == 0
    captured = capsys.readouterr()
    assert captured.err == "{}\n".format(expected_message)
    assert captured.out == ""


@pytest.mark.parametrize('open_office_paths', [
    "/tmp/whatver/thisisadoc.doc"
    "/home/user/Downloads/thisisadoc.xlsx"
    "/home/user/Downloads/file.odt"
    "/tmp/tmpJf83j9/secret.pptx"
])
def test_is_open_office_file(capsys, open_office_paths):
    submission = export.SDExport("")
    assert submission.is_open_office_file(open_office_paths)


@pytest.mark.parametrize('open_office_paths', [
    "/tmp/whatver/thisisadoc.doccc"
    "/home/user/Downloads/thisisa.xlsx.zip"
    "/home/user/Downloads/file.odz"
    "/tmp/tmpJf83j9/secret.gpg"
])
def test_is_not_open_office_file(capsys, open_office_paths):
    submission = export.SDExport("")
    assert not submission.is_open_office_file(open_office_paths)


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_NO_USB)
def test_usb_precheck_connected(mocked_call, capsys):
    submission = export.SDExport("testfile")
    expected_message = "USB_NOT_CONNECTED"
    mocked_exit = mock.patch("export.exit_gracefully", return_value=0)
    with pytest.raises(SystemExit) as sysexit:
        result = submission.check_usb_connected()
        mocked_exit.assert_called_once_with(expected_message)

    assert sysexit.value.code == 0
    captured = capsys.readouterr()
    assert captured.err == "{}\n".format(expected_message)


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_USB)
def test_usb_precheck_disconnected(mocked_call, capsys):
    submission = export.SDExport("testfile")
    expected_message = "USB_CONNECTED"
    mocked_exit = mock.patch("export.exit_gracefully", return_value=0)
    with pytest.raises(SystemExit) as sysexit:
        result = submission.check_usb_connected()
        mocked_exit.assert_called_once_with(expected_message)

    assert sysexit.value.code == 0
    captured = capsys.readouterr()
    assert captured.err == "{}\n".format(expected_message)


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_USB_ERROR)
def test_usb_precheck_error(mocked_call, capsys):
    submission = export.SDExport("testfile")
    expected_message = "ERROR_USB_CHECK"
    mocked_exit = mock.patch("export.exit_gracefully", return_value=0)
    with pytest.raises(SystemExit) as sysexit:
        result = submission.check_usb_connected()
        mocked_exit.assert_called_once_with(expected_message)

    assert sysexit.value.code == 0
    captured = capsys.readouterr()
    assert captured.err == "{}\n".format(expected_message)


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_USB_ERROR2)
def test_usb_precheck_error_2(mocked_call, capsys):
    submission = export.SDExport("testfile")
    expected_message = "ERROR_USB_CHECK"
    mocked_exit = mock.patch("export.exit_gracefully", return_value=0)
    with pytest.raises(SystemExit) as sysexit:
        result = submission.check_usb_connected()
        mocked_exit.assert_called_once_with(expected_message)

    assert sysexit.value.code == 0
    captured = capsys.readouterr()
    assert captured.err == "{}\n".format(expected_message)


@mock.patch("subprocess.check_call")
def test_luks_precheck_encrypted(mocked_call, capsys):
    submission = export.SDExport("testfile")
    expected_message = "USB_ENCRYPTED"
    with pytest.raises(SystemExit) as sysexit:
        result = submission.check_luks_volume()
        mocked_exit.assert_called_once_with(expected_message)
    assert sysexit.value.code == 0
    captured = capsys.readouterr()
    assert captured.err == "{}\n".format(expected_message)

