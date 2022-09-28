from unittest import mock

import os
import pytest
from subprocess import CalledProcessError
import sys

from securedrop_export.exceptions import ExportException
from securedrop_export.archive import Archive
from securedrop_export.print.service import Service
from securedrop_export.print.service import Status


SAMPLE_OUTPUT_NO_PRINTER = b"network beh\nnetwork https\nnetwork ipp\nnetwork ipps\nnetwork http\nnetwork\nnetwork ipp14\nnetwork lpd"  # noqa
SAMPLE_OUTPUT_BROTHER_PRINTER = b"network beh\nnetwork https\nnetwork ipp\nnetwork ipps\nnetwork http\nnetwork\nnetwork ipp14\ndirect usb://Brother/HL-L2320D%20series?serial=A00000A000000\nnetwork lpd"  # noqa
SAMPLE_OUTPUT_LASERJET_PRINTER = b"network beh\nnetwork https\nnetwork ipp\nnetwork ipps\nnetwork http\nnetwork\nnetwork ipp14\ndirect usb://HP/LaserJet%20Pro%20M404-M405?serial=A00000A000000\nnetwork lpd"  # noqa
TEST_CONFIG = os.path.join(os.path.dirname(__file__), "sd-export-config.json")


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_BROTHER_PRINTER)
def test_get_good_printer_uri_laserjet(mocked_call):
    submission = Archive("testfile", TEST_CONFIG)
    service = Service(submission)

    result = service._get_printer_uri()

    assert result == "usb://Brother/HL-L2320D%20series?serial=A00000A000000"


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_LASERJET_PRINTER)
def test_get_good_printer_uri_brother(mocked_call):
    submission = Archive("testfile", TEST_CONFIG)
    service = Service(submission)

    result = service._get_printer_uri()
    assert result == "usb://HP/LaserJet%20Pro%20M404-M405?serial=A00000A000000"


@mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_NO_PRINTER)
def test_get_bad_printer_uri(mocked_call, capsys, mocker):
    submission = Archive("testfile", TEST_CONFIG)
    service = Service(submission)
    expected_status = Status.ERROR_PRINTER_NOT_FOUND # todo

    with pytest.raises(ExportException):
        service._get_printer_uri()


@pytest.mark.parametrize(
    "open_office_paths",
    [
        "/tmp/whatver/thisisadoc.doc"
        "/home/user/Downloads/thisisadoc.xlsx"
        "/home/user/Downloads/file.odt"
        "/tmp/tmpJf83j9/secret.pptx"
    ],
)
def test_is_open_office_file(capsys, open_office_paths):
    submission = Archive("", TEST_CONFIG)
    service = Service(submission)
    assert service._is_open_office_file(open_office_paths)


@pytest.mark.parametrize(
    "open_office_paths",
    [
        "/tmp/whatver/thisisadoc.doccc"
        "/home/user/Downloads/thisisa.xlsx.zip"
        "/home/user/Downloads/file.odz"
        "/tmp/tmpJf83j9/secret.gpg"
    ],
)
def test_is_not_open_office_file(capsys, open_office_paths):
    submission = Archive("", TEST_CONFIG)
    service = Service(submission)
    assert not service._is_open_office_file(open_office_paths)


@mock.patch("subprocess.run")
def test_install_printer_ppd_laserjet(mocker):
    submission = Archive("testfile", TEST_CONFIG)
    service = Service(submission)
    ppd = service._install_printer_ppd("usb://HP/LaserJet%20Pro%20M404-M405?serial=A00000A00000")
    assert ppd == "/usr/share/cups/model/hp-laserjet_6l.ppd"


@mock.patch("subprocess.run")
def test_install_printer_ppd_brother(mocker):
    submission = Archive("testfile", TEST_CONFIG)
    service = Service(submission)
    ppd = service._install_printer_ppd("usb://Brother/HL-L2320D%20series?serial=A00000A000000")
    assert ppd == "/usr/share/cups/model/br7030.ppd"


def test_install_printer_ppd_error_no_driver(mocker):
    submission = Archive("testfile", TEST_CONFIG)
    service = Service(submission)

    mocker.patch("subprocess.run", side_effect=CalledProcessError(1, "run"))

    with pytest.raises(ExportException) as ex:
        service._install_printer_ppd("usb://HP/LaserJet%20Pro%20M404-M405?serial=A00000A000000")

    assert ex.value.sdstatus is Status.ERROR_PRINTER_DRIVER_UNAVAILABLE


def test_install_printer_ppd_error_not_supported(mocker):
    submission = Archive("testfile", TEST_CONFIG)
    service = Service(submission)
    mocker.patch("subprocess.run", side_effect=CalledProcessError(1, "run"))

    with pytest.raises(ExportException) as ex:
        service._install_printer_ppd("usb://Not/Supported?serial=A00000A000000")

    assert ex.value.sdstatus is Status.ERROR_PRINTER_NOT_SUPPORTED


def test_setup_printer_error(mocker):
    submission = Archive("testfile", TEST_CONFIG)
    service = Service(submission)
    
    mocker.patch("subprocess.run", side_effect=CalledProcessError(1, "run"))

    with pytest.raises(ExportException) as ex:
        service._setup_printer(
            "usb://Brother/HL-L2320D%20series?serial=A00000A000000",
            "/usr/share/cups/model/br7030.ppd",
        )

    assert ex.value.sdstatus is Status.ERROR_PRINTER_INSTALL