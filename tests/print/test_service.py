import pytest

from unittest import mock
import os
import subprocess
from subprocess import CalledProcessError

from securedrop_export.directory_util import safe_mkdir

from securedrop_export.exceptions import ExportException
from securedrop_export.archive import Archive
from securedrop_export.print.service import Service
from securedrop_export.print.status import Status

SAMPLE_OUTPUT_NO_PRINTER = b"network beh\nnetwork https\nnetwork ipp\nnetwork ipps\nnetwork http\nnetwork\nnetwork ipp14\nnetwork lpd"  # noqa
SAMPLE_OUTPUT_BROTHER_PRINTER = b"network beh\nnetwork https\nnetwork ipp\nnetwork ipps\nnetwork http\nnetwork\nnetwork ipp14\ndirect usb://Brother/HL-L2320D%20series?serial=A00000A000000\nnetwork lpd"  # noqa
SAMPLE_OUTPUT_LASERJET_PRINTER = b"network beh\nnetwork https\nnetwork ipp\nnetwork ipps\nnetwork http\nnetwork\nnetwork ipp14\ndirect usb://HP/LaserJet%20Pro%20M404-M405?serial=A00000A000000\nnetwork lpd"  # noqa
SAMPLE_OUTPUT_UNSUPPORTED_PRINTER = b"network beh\nnetwork https\nnetwork ipp\nnetwork ipps\nnetwork http\nnetwork\nnetwork ipp14\ndirect usb://Canon/QL-700%?serial=A00000A000000\nnetwork lpd"  # noqa


class TestPrint:
    @classmethod
    def setup_class(cls):
        cls.submission = Archive("testfile")
        cls.service = Service(cls.submission)

        # Set up files as if extracted from tarball
        fp = os.path.join(cls.submission.tmpdir, "export_data")
        if not os.path.exists(fp):
            safe_mkdir(fp)

        for i in ["file1", "file2", "file3"]:
            with open(f"{cls.submission.tmpdir}/export_data/{i}.txt", "a+") as file:
                file.write(f"It's a pretend file {i}")
                file.write("\n")

    @classmethod
    def teardown_class(cls):
        cls.service = None
        cls.submission = None

    @mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_BROTHER_PRINTER)
    def test_get_good_printer_uri_laserjet(self, mocked_call):
        assert (
            self.service._get_printer_uri()
            == "usb://Brother/HL-L2320D%20series?serial=A00000A000000"
        )

    def test_service_initialized_correctly(self):
        assert self.service.printer_wait_timeout == 60
        assert self.service.printer_name == "sdw-printer"

    def test_print_all_methods_called(self):
        patch_setup = mock.patch.object(self.service, "_check_printer_setup")
        patch_print = mock.patch.object(self.service, "_print_all_files")

        mock_setup = patch_setup.start()
        mock_print = patch_print.start()

        self.service.print()

        # When the client can accept new status values, we will assert that the
        # above call results in Status.PRINT_SUCCESS
        assert mock_setup.called_once()
        assert mock_print.called_once()

        patch_setup.stop()
        patch_print.stop()

    def test_printer_test_all_methods_called(self):
        patch_setup = mock.patch.object(self.service, "_check_printer_setup")

        mock_setup = patch_setup.start()

        self.service.printer_preflight()

        # When the client can accept new status values, we will assert that the
        # above call results in Status.PREFLIGHT_SUCCESS
        assert mock_setup.called_once()

        patch_setup.stop()

    def test_print_all_checks_called(self):
        patch_setup = mock.patch.object(self.service, "_check_printer_setup")
        patch_print = mock.patch.object(self.service, "_print_test_page")

        mock_setup = patch_setup.start()
        mock_print = patch_print.start()

        self.service.printer_test()
        # When the client can accept new status values, we will assert that the
        # above call results in Status.TEST_SUCCESS

        assert mock_setup.called_once()
        assert mock_print.called_once()

        patch_setup.stop()
        patch_print.stop()

    @mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_LASERJET_PRINTER)
    def test_get_good_printer_uri_brother(self, mocked_call):
        assert (
            self.service._get_printer_uri()
            == "usb://HP/LaserJet%20Pro%20M404-M405?serial=A00000A000000"
        )

    @mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_NO_PRINTER)
    def test_get_bad_printer_uri(self, mocked_call, capsys, mocker):
        with pytest.raises(ExportException) as ex:
            self.service._get_printer_uri()

        assert ex.value.sdstatus is Status.ERROR_PRINTER_NOT_FOUND

    @pytest.mark.parametrize(
        "open_office_paths",
        [
            "/tmp/whatver/thisisadoc.doc"
            "/home/user/Downloads/thisisadoc.xlsx"
            "/home/user/Downloads/file.odt"
            "/tmp/tmpJf83j9/secret.pptx"
        ],
    )
    def test_is_open_office_file(self, capsys, open_office_paths):
        assert self.service._is_open_office_file(open_office_paths)

    @pytest.mark.parametrize(
        "open_office_paths",
        [
            "/tmp/whatver/thisisadoc.doccc"
            "/home/user/Downloads/thisisa.xlsx.zip"
            "/home/user/Downloads/file.odz"
            "/tmp/tmpJf83j9/secret.gpg"
        ],
    )
    def test_is_not_open_office_file(self, capsys, open_office_paths):
        assert not self.service._is_open_office_file(open_office_paths)

    @mock.patch("subprocess.run")
    def test_install_printer_ppd_laserjet(self, mocker):
        ppd = self.service._install_printer_ppd(
            "usb://HP/LaserJet%20Pro%20M404-M405?serial=A00000A00000"
        )
        assert ppd == "/usr/share/cups/model/hp-laserjet_6l.ppd"

    @mock.patch("subprocess.run")
    def test_install_printer_ppd_brother(self, mocker):
        ppd = self.service._install_printer_ppd(
            "usb://Brother/HL-L2320D%20series?serial=A00000A000000"
        )
        assert ppd == "/usr/share/cups/model/br7030.ppd"

    def test_install_printer_ppd_error_no_driver(self, mocker):
        mocker.patch("subprocess.run", side_effect=CalledProcessError(1, "run"))

        with pytest.raises(ExportException) as ex:
            self.service._install_printer_ppd(
                "usb://HP/LaserJet%20Pro%20M404-M405?serial=A00000A000000"
            )

        assert ex.value.sdstatus is Status.ERROR_PRINTER_DRIVER_UNAVAILABLE

    def test_install_printer_ppd_error_not_supported(self, mocker):
        mocker.patch("subprocess.run", side_effect=CalledProcessError(1, "run"))

        with pytest.raises(ExportException) as ex:
            self.service._install_printer_ppd(
                "usb://Not/Supported?serial=A00000A000000"
            )

        assert ex.value.sdstatus is Status.ERROR_PRINTER_NOT_SUPPORTED

    def test_setup_printer_error(self, mocker):
        mocker.patch("subprocess.run", side_effect=CalledProcessError(1, "run"))

        with pytest.raises(ExportException) as ex:
            self.service._setup_printer(
                "usb://Brother/HL-L2320D%20series?serial=A00000A000000",
                "/usr/share/cups/model/br7030.ppd",
            )

        assert ex.value.sdstatus is Status.ERROR_PRINTER_INSTALL

    def test_safe_check_call(self):
        # This works, since `ls` is a valid comand
        self.service.safe_check_call(["ls"], Status.TEST_SUCCESS)

    def test_safe_check_call_invalid_call(self):
        with pytest.raises(ExportException) as ex:
            self.service.safe_check_call(["ls", "kjdsfhkdjfh"], Status.ERROR_PRINT)

        assert ex.value.sdstatus is Status.ERROR_PRINT

    def test_safe_check_call_write_to_stderr_and_ignore_error(self):
        self.service.safe_check_call(
            ["python3", "-c", "import sys;sys.stderr.write('hello')"],
            error_status=Status.TEST_SUCCESS,
            ignore_stderr_startswith=b"hello",
        )

    def test_safe_check_call_write_to_stderr_wrong_ignore_param(self):
        # This one writes to stderr and ignores the wrong string, so we expect an exception
        with pytest.raises(ExportException) as ex:
            self.service.safe_check_call(
                ["python3", "-c", "import sys;sys.stderr.write('hello\n')"],
                error_status=Status.ERROR_PRINT,
                ignore_stderr_startswith=b"world",
            )

        assert ex.value.sdstatus is Status.ERROR_PRINT

    @mock.patch("time.sleep", return_value=None)
    @mock.patch(
        "subprocess.check_output",
        side_effect=[
            b"printer sdw-printer is busy\n",
            b"printer sdw-printer is idle\n",
        ],
    )
    def test__wait_for_print(self, mock_subprocess, mock_time):
        assert self.service._wait_for_print()

    @mock.patch("time.sleep", return_value=None)
    @mock.patch(
        "subprocess.check_output",
        side_effect=subprocess.CalledProcessError(1, "check_output"),
    )
    def test__wait_for_print_print_exception(self, mock_subprocess, mock_time):
        with pytest.raises(ExportException) as ex:
            self.service._wait_for_print()

        assert ex.value.sdstatus is Status.ERROR_PRINT

    @mock.patch(
        "subprocess.check_output", return_value=b"printer sdw-printer is busy\n"
    )
    def test__wait_for_print_timeout_exception(self, mock_subprocess):
        self.service.printer_wait_timeout = 1

        with pytest.raises(ExportException) as ex:
            self.service._wait_for_print()

        assert ex.value.sdstatus is Status.ERROR_PRINT

        self.service.printer_wait_timeout = self.service.PRINTER_WAIT_TIMEOUT

    @pytest.mark.parametrize(
        "printers", [SAMPLE_OUTPUT_BROTHER_PRINTER, SAMPLE_OUTPUT_LASERJET_PRINTER]
    )
    def test__check_printer_setup(self, printers, mocker):
        mocker.patch("subprocess.check_output", return_value=printers)
        p = mocker.patch.object(self.service, "_setup_printer")
        p2 = mocker.patch.object(self.service, "_install_printer_ppd")
        p.start()
        p2.start()

        self.service._check_printer_setup()
        p.assert_called_once()
        p2.assert_called_once()

        p.stop()
        p2.stop()

    @mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_NO_PRINTER)
    def test__check_printer_setup_error_no_printer(self, mock_output):

        with pytest.raises(ExportException) as ex:
            self.service._check_printer_setup()
        assert ex.value.sdstatus is Status.ERROR_PRINTER_NOT_FOUND

    @mock.patch(
        "subprocess.check_output",
        return_value=SAMPLE_OUTPUT_BROTHER_PRINTER
        + b"\n"
        + SAMPLE_OUTPUT_LASERJET_PRINTER,
    )
    def test__check_printer_setup_error_too_many_printers(self, mock_output):

        with pytest.raises(ExportException) as ex:
            self.service._check_printer_setup()
        assert ex.value.sdstatus is Status.ERROR_MULTIPLE_PRINTERS_FOUND

    @mock.patch(
        "subprocess.check_output", return_value=SAMPLE_OUTPUT_UNSUPPORTED_PRINTER
    )
    def test__check_printer_setup_error_unsupported_printer(self, mock_output):

        with pytest.raises(ExportException) as ex:
            self.service._check_printer_setup()
        assert ex.value.sdstatus is Status.ERROR_PRINTER_NOT_SUPPORTED

    @mock.patch(
        "subprocess.check_output",
        side_effect=subprocess.CalledProcessError(1, "check_output"),
    )
    def test__check_printer_setup_error_checking_printer(self, mock_output):

        with pytest.raises(ExportException) as ex:
            self.service._check_printer_setup()
        assert ex.value.sdstatus is Status.ERROR_UNKNOWN

    @mock.patch(
        "subprocess.check_output",
        side_effect=subprocess.CalledProcessError(1, "check_output"),
    )
    def test__get_printer_uri_error(self, mocked_subprocess):
        with pytest.raises(ExportException) as ex:
            self.service._get_printer_uri()
        assert ex.value.sdstatus is Status.ERROR_PRINTER_URI

    @mock.patch(
        "subprocess.check_output", return_value=SAMPLE_OUTPUT_UNSUPPORTED_PRINTER
    )
    def test__get_printer_uri_error_unsupported(self, mocked_subprocess):
        with pytest.raises(ExportException) as ex:
            self.service._get_printer_uri()
        assert ex.value.sdstatus is Status.ERROR_PRINTER_NOT_SUPPORTED

    def test__install_printer_ppd_error_unsupported_uri(self):
        with pytest.raises(ExportException) as ex:
            self.service._install_printer_ppd(
                "usb://YOURE_NOT_MY_REAL_PRINTER/A00000A000000"
            )
        assert ex.value.sdstatus is Status.ERROR_PRINTER_NOT_SUPPORTED

    def test__print_test_page_calls_method(self):
        p = mock.patch.object(self.service, "_print_file")
        mock_print = p.start()

        self.service._print_test_page()
        mock_print.assert_called_once_with("/usr/share/cups/data/testprint")
        p.stop()

    def test__print_all_files(self):
        p = mock.patch.object(self.service, "_print_file")
        mock_print = p.start()

        self.service._print_all_files()
        mock_print.assert_has_calls(
            [
                mock.call(f"{self.submission.tmpdir}/export_data/file1.txt"),
                mock.call(f"{self.submission.tmpdir}/export_data/file2.txt"),
                mock.call(f"{self.submission.tmpdir}/export_data/file3.txt"),
            ],
            any_order=True,
        )
        p.stop()

    def test_open_office_file_convert_to_pdf(self):
        file = "/tmp/definitely-an-office-file.odt"

        with mock.patch.object(self.service, "safe_check_call") as scc, mock.patch(
            "securedrop_export.print.service.logger.info"
        ) as log:
            self.service._print_file(file)

        assert scc.call_count == 2
        scc.assert_has_calls(
            [
                mock.call(
                    command=[
                        "unoconv",
                        "-o",
                        "/tmp/definitely-an-office-file.odt.pdf",
                        "/tmp/definitely-an-office-file.odt",
                    ],
                    error_status=Status.ERROR_PRINT,
                ),
                mock.call(
                    command=[
                        "xpp",
                        "-P",
                        "sdw-printer",
                        "/tmp/definitely-an-office-file.odt.pdf",
                    ],
                    error_status=Status.ERROR_PRINT,
                ),
            ]
        )
        assert log.call_count == 2
        log.assert_has_calls(
            [
                mock.call("Converting Office document to pdf"),
                mock.call("Sending file to printer sdw-printer"),
            ]
        )

    def test_safe_check_call_has_error_in_stderr(self):
        mock.patch("subprocess.run")

        with mock.patch("subprocess.run"), pytest.raises(ExportException) as ex:
            self.service.safe_check_call(command="ls", error_status=Status.TEST_SUCCESS)

        assert ex.value.sdstatus is Status.TEST_SUCCESS
