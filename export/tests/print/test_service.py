import os
import shutil
import subprocess
import tempfile
from pathlib import Path
from subprocess import CalledProcessError
from unittest import mock

import pytest

from securedrop_export.archive import Archive
from securedrop_export.directory import safe_mkdir
from securedrop_export.exceptions import ExportException
from securedrop_export.print.service import Service
from securedrop_export.print.status import Status

SAMPLE_OUTPUT_NO_PRINTER = b"network beh\nnetwork https\nnetwork ipp\nnetwork ipps\nnetwork http\nnetwork\nnetwork ipp14\nnetwork lpd"  # noqa
SAMPLE_OUTPUT_BROTHER_PRINTER = b"network beh\nnetwork https\nnetwork ipp\nnetwork ipps\nnetwork http\nnetwork\nnetwork ipp14\ndirect usb://Brother/HL-L2320D%20series?serial=A00000A000000\nnetwork lpd"  # noqa
SAMPLE_OUTPUT_LASERJET_PRINTER = b"network beh\nnetwork https\nnetwork ipp\nnetwork ipps\nnetwork http\nnetwork\nnetwork ipp14\ndirect usb://HP/LaserJet%20Pro%20M404-M405?serial=A00000A000000\nnetwork lpd"  # noqa
SAMPLE_OUTPUT_UNSUPPORTED_PRINTER = b"network beh\nnetwork https\nnetwork ipp\nnetwork ipps\nnetwork http\nnetwork\nnetwork ipp14\ndirect usb://Canon/QL-700%?serial=A00000A000000\nnetwork lpd"  # noqa

SUPPORTED_MIMETYPE_COUNT = 107  # Mimetypes in the sample LibreOffice .desktop files
SAMPLE_FILES_SUPPORTED = Path.cwd() / "tests" / "files" / "samples_supported"
SAMPLE_FILES_UNSUPPORTED = Path.cwd() / "tests" / "files" / "samples_unsupported"


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

    def setup_method(self):
        self.service.printer_wait_timeout = self.service.PRINTER_WAIT_TIMEOUT

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

    @mock.patch("securedrop_export.print.service.Service._wait_for_print")
    def test_printer_preflight_all_methods_called(self, mock_wait):
        patch_setup = mock.patch.object(self.service, "_check_printer_setup")

        mock_setup = patch_setup.start()

        self.service.printer_preflight()

        # When the client can accept new status values, we will assert that the
        # above call results in Status.PREFLIGHT_SUCCESS
        assert mock_setup.called_once()

        patch_setup.stop()

    @mock.patch("securedrop_export.print.service.Service._wait_for_print")
    def test_print_testpage_all_checks_called(self, mock_wait):
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

    @mock.patch(
        "subprocess.check_output",
        return_value=b"/path/to/I Have Spaces.odg: application/vnd.oasis.opendocument.graphics\n",
    )
    def test_needs_pdf_conversion(self, capsys):
        file = tempfile.NamedTemporaryFile()

        testdir_libreoffice_desktop = Path.cwd() / "tests" / "files"
        supported = self.service._get_supported_mimetypes_libreoffice(testdir_libreoffice_desktop)
        with mock.patch.object(
            self.service, "_get_supported_mimetypes_libreoffice", return_value=supported
        ):
            self.service._needs_pdf_conversion(file)

    def test__get_supported_mimetypes_libreoffice(self, capsys):
        """
        Given well-formatted libreoffice sample .desktop files, assert correctly parsed.
        """
        # sample .desktop files in test directory, but the service checks /usr/share/applications
        testdir_libreoffice_desktop = Path.cwd() / "tests" / "files"
        supported = self.service._get_supported_mimetypes_libreoffice(testdir_libreoffice_desktop)
        assert len(supported) == SUPPORTED_MIMETYPE_COUNT

    def test__get_supported_mimetypes_libreoffice_handles_error(self, capsys):
        """
        Given missing libreoffice sample .desktop files, assert error-handling.
        """
        with tempfile.TemporaryDirectory() as tmpdir_no_libreoffice_files:
            result = self.service._get_supported_mimetypes_libreoffice(tmpdir_no_libreoffice_files)
            assert len(result) == 0

    def test__get_supported_mimetypes_libreoffice_integration(self, capsys):
        """If LibreOffice is installed for real, test against it"""
        apps = Path("/usr/share/applications")
        if not (apps / "libreoffice-writer.desktop").exists():
            pytest.skip("libreoffice doesn't appear to be installed")

        mimes = self.service._get_supported_mimetypes_libreoffice(apps)
        # Check some basic formats (odt and docx)
        assert "application/vnd.oasis.opendocument.text" in mimes
        assert "application/vnd.openxmlformats-officedocument.wordprocessingml.document" in mimes

    @pytest.mark.parametrize("sample_file", [i for i in os.listdir(SAMPLE_FILES_SUPPORTED)])
    def test__print_file_with_libreoffice_conversion_integration(self, sample_file, capsys):
        apps = Path("/usr/share/applications")
        if not (apps / "libreoffice-writer.desktop").exists():
            pytest.skip("libreoffice doesn't appear to be installed")

        # Set up a sample print directory with a real file
        print_dir = tempfile.TemporaryDirectory()
        filepath = SAMPLE_FILES_SUPPORTED / sample_file
        shutil.copy(filepath, print_dir.name)

        target = Path(print_dir.name, sample_file)

        if self.service._needs_pdf_conversion(target):
            expected = target.parent / "print-pdf" / (target.stem + ".pdf")
        else:
            expected = target

        with (
            mock.patch("subprocess.check_call") as mock_print_xpp,
            mock.patch.object(self.service, "_wait_for_print") as mock_wait_for_print,
        ):
            self.service._print_file(target)

        assert expected.exists()
        assert mock_wait_for_print.call_count == 1
        assert mock_print_xpp.call_count == 1
        mock_print_xpp.assert_has_calls(
            [
                mock.call(
                    [
                        "xpp",
                        "-P",
                        "sdw-printer",
                        expected,
                    ],
                ),
            ]
        )

    @pytest.mark.parametrize("sample_file", [i for i in os.listdir(SAMPLE_FILES_UNSUPPORTED)])
    def test__print_file_unsupported_integration(self, sample_file, capsys):
        apps = Path("/usr/share/applications")
        if not (apps / "libreoffice-writer.desktop").exists():
            pytest.skip("libreoffice doesn't appear to be installed")

        # Set up a sample print directory with a real file
        print_dir = tempfile.TemporaryDirectory()
        filepath = SAMPLE_FILES_UNSUPPORTED / sample_file
        shutil.copy(filepath, print_dir.name)

        target = Path(print_dir.name, sample_file)

        with pytest.raises(ExportException) as ex:
            self.service._print_file(target)

        assert ex.value.sdstatus == Status.ERROR_MIMETYPE_UNSUPPORTED

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
            self.service._install_printer_ppd("usb://Not/Supported?serial=A00000A000000")

        assert ex.value.sdstatus is Status.ERROR_PRINTER_NOT_SUPPORTED

    def test_setup_printer_error(self, mocker):
        mocker.patch("subprocess.run", side_effect=CalledProcessError(1, "run"))

        with pytest.raises(ExportException) as ex:
            self.service._setup_printer(
                "usb://Brother/HL-L2320D%20series?serial=A00000A000000",
                "/usr/share/cups/model/br7030.ppd",
            )

        assert ex.value.sdstatus is Status.ERROR_PRINTER_INSTALL

    def test_check_output_and_stderr(self):
        # This works, since `ls` is a valid comand
        self.service.check_output_and_stderr(["ls"], Status.PRINT_TEST_PAGE_SUCCESS)

    def test_safe_check_output_invalid_call(self):
        with pytest.raises(ExportException) as ex:
            self.service.check_output_and_stderr(["ls", "kjdsfhkdjfh"], Status.ERROR_PRINT)

        assert ex.value.sdstatus is Status.ERROR_PRINT

    def test_safe_check_output_write_to_stderr_and_ignore_error(self):
        self.service.check_output_and_stderr(
            ["python3", "-c", "import sys;sys.stderr.write('hello')"],
            error_status=Status.PRINT_TEST_PAGE_SUCCESS,
            ignore_stderr_startswith=b"hello",
        )

    def test_safe_check_output_write_to_stderr_wrong_ignore_param(self):
        # This one writes to stderr and ignores the wrong string, so we expect an exception
        with pytest.raises(ExportException) as ex:
            self.service.check_output_and_stderr(
                ["python3", "-c", "import sys;sys.stderr.write('hello\n')"],
                error_status=Status.ERROR_PRINT,
                ignore_stderr_startswith=b"world",
            )

        assert ex.value.sdstatus is Status.ERROR_PRINT

    @mock.patch("securedrop_export.print.service.time.sleep", return_value=None)
    @mock.patch(
        "subprocess.check_output",
        side_effect=[
            b"printer sdw-printer is busy\n",
            b"printer sdw-printer is idle\n",
        ],
    )
    def test__wait_for_print(self, mock_subprocess, mock_time):
        assert self.service._wait_for_print()

    @mock.patch(
        "subprocess.check_output",
        side_effect=subprocess.CalledProcessError(1, "check_output"),
    )
    @mock.patch("time.sleep", return_value=None)
    def test__wait_for_print_print_exception(self, mock_time, mock_subprocess):
        with pytest.raises(ExportException) as ex:
            self.service._wait_for_print()

        assert ex.value.sdstatus is Status.ERROR_PRINT

    @mock.patch("subprocess.check_output", return_value=b"printer sdw-printer is busy\n")
    def test__wait_for_print_timeout_exception(self, mock_output):
        self.service.printer_wait_timeout = 1

        with pytest.raises(ExportException) as ex:
            self.service._wait_for_print()

        assert ex.value.sdstatus is Status.ERROR_PRINT

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
        return_value=SAMPLE_OUTPUT_BROTHER_PRINTER + b"\n" + SAMPLE_OUTPUT_LASERJET_PRINTER,
    )
    def test__check_printer_setup_error_too_many_printers(self, mock_output):
        with pytest.raises(ExportException) as ex:
            self.service._check_printer_setup()
        assert ex.value.sdstatus is Status.ERROR_MULTIPLE_PRINTERS_FOUND

    @mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_UNSUPPORTED_PRINTER)
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

    @mock.patch("subprocess.check_output", return_value=SAMPLE_OUTPUT_UNSUPPORTED_PRINTER)
    def test__get_printer_uri_error_unsupported(self, mocked_subprocess):
        with pytest.raises(ExportException) as ex:
            self.service._get_printer_uri()
        assert ex.value.sdstatus is Status.ERROR_PRINTER_NOT_SUPPORTED

    def test__install_printer_ppd_error_unsupported_uri(self):
        with pytest.raises(ExportException) as ex:
            self.service._install_printer_ppd("usb://YOURE_NOT_MY_REAL_PRINTER/A00000A000000")
        assert ex.value.sdstatus is Status.ERROR_PRINTER_NOT_SUPPORTED

    @mock.patch("securedrop_export.print.service.Service._wait_for_print")
    def test__print_test_page_calls_method(self, mock_wait):
        p = mock.patch.object(self.service, "_print_file")
        mock_print = p.start()

        self.service._print_test_page()
        mock_print.assert_called_once_with(Path("/usr/share/cups/data/testprint"))
        p.stop()

    @mock.patch("securedrop_export.print.service.Service._wait_for_print")
    def test__print_all_files(self, mock_wait):
        p = mock.patch.object(self.service, "_print_file")
        mock_print = p.start()

        self.service._print_all_files()
        mock_print.assert_has_calls(
            [
                mock.call(Path(self.submission.tmpdir, "export_data/file1.txt")),
                mock.call(Path(self.submission.tmpdir, "export_data/file2.txt")),
                mock.call(Path(self.submission.tmpdir, "export_data/file3.txt")),
            ],
            any_order=True,
        )
        p.stop()

    @mock.patch("securedrop_export.print.service.Service._wait_for_print")
    def test__print_file_odt_calls_libreoffice_conversion_then_print(self, mock_wait):
        print_dir = tempfile.TemporaryDirectory()
        filepath = Path(print_dir.name, "office.odg")
        expected_conversion_file = filepath.parent / "print-pdf" / (filepath.stem + ".pdf")

        with (
            mock.patch.object(self.service, "_needs_pdf_conversion", return_value=True),
            mock.patch("subprocess.check_call") as check_call,
            mock.patch("securedrop_export.print.service.logger.info") as log,
            mock.patch(
                "subprocess.check_output",
                side_effect=[
                    b"/tmp/export-data/office-file.odt: application/vnd.oasis.opendocument.text\n",
                    b"Convert office-file.odt -> office-file.pdf using filter: writer_pdf_Export\n",
                ],
            ) as check_output,
            mock.patch("pathlib.Path.exists", side_effect=[True, False, True]),
            # A bit hacky, but: return True (check directory permissions of print-pdf dir),
            # False (no existing file that would be overwritten), True (target file exists)
        ):
            self.service._print_file(filepath)

        assert check_output.call_count == 1

        check_output.assert_has_calls(
            [
                mock.call(
                    [
                        "libreoffice",
                        "--headless",
                        "--safe-mode",
                        "--convert-to",
                        "pdf",
                        "--outdir",
                        Path(filepath.parent / "print-pdf"),
                        filepath,
                    ],
                )
            ]
        )
        assert check_call.call_count == 1
        check_call.assert_has_calls(
            [
                mock.call(
                    [
                        "xpp",
                        "-P",
                        "sdw-printer",
                        expected_conversion_file,
                    ],
                ),
            ]
        )
        assert log.call_count == 2
        log.assert_has_calls(
            [
                mock.call("Convert to pdf for printing"),
                mock.call("Sending file to printer sdw-printer"),
            ]
        )

    @mock.patch("securedrop_export.print.service.Service._wait_for_print")
    def test__print_file_raises_if_file_not_found(self, mock_wait):
        print_dir = tempfile.TemporaryDirectory()
        filepath = Path(print_dir.name, "office.odg")
        expected_conversion_file = filepath.parent / "print-pdf" / (filepath.stem + ".pdf")

        with (
            mock.patch("securedrop_export.print.service.logger.error") as log,
            mock.patch.object(self.service, "_needs_pdf_conversion", return_value=True),
            mock.patch(
                "subprocess.check_output",
                side_effect=[
                    b"/tmp/export-data/office-file.odt: application/vnd.oasis.opendocument.text\n",
                    b"Convert office-file.odt -> office-file.pdf\n",
                ],
            ) as check_output,
            pytest.raises(ExportException) as ex,
        ):
            self.service._print_file(filepath)

        assert ex.value.sdstatus == Status.ERROR_PRINT

        assert check_output.call_count == 1
        check_output.assert_has_calls(
            [
                mock.call(
                    [
                        "libreoffice",
                        "--headless",
                        "--safe-mode",
                        "--convert-to",
                        "pdf",
                        "--outdir",
                        expected_conversion_file.parent,
                        filepath,
                    ],
                )
            ]
        )
        assert log.call_count == 1
        log.assert_has_calls(
            [
                mock.call(f"Something went wrong: {expected_conversion_file} not found"),
            ]
        )

    def test_safe_check_output_has_error_in_stderr(self):
        mock.patch("subprocess.run")

        with mock.patch("subprocess.run"), pytest.raises(ExportException) as ex:
            self.service.check_output_and_stderr(
                command="ls", error_status=Status.PRINT_TEST_PAGE_SUCCESS
            )

        assert ex.value.sdstatus is Status.PRINT_TEST_PAGE_SUCCESS

    @mock.patch("securedrop_export.print.service.time.sleep", return_value=None)
    @mock.patch(
        "subprocess.check_output",
        side_effect=[
            b"printer sdw-printer is busy\n",
            b"printer sdw-printer is idle\n",
        ],
    )
    def test__wait_for_print_waits_correctly(self, mock_sp, mock_time):
        file = tempfile.NamedTemporaryFile()
        filepath = Path(file.name)

        with (
            mock.patch("subprocess.check_call") as mock_subprocess,
            mock.patch("securedrop_export.print.service.logger.info") as log,
            mock.patch.object(self.service, "_needs_pdf_conversion", return_value=False),
        ):
            self.service._print_file(filepath)

        assert mock_subprocess.call_count == 1
        mock_subprocess.assert_has_calls(
            [
                mock.call(
                    [
                        "xpp",
                        "-P",
                        "sdw-printer",
                        filepath,
                    ],
                ),
            ]
        )
        assert log.call_count == 4
        log.assert_has_calls(
            [
                mock.call("Sending file to printer sdw-printer"),
                mock.call("Running lpstat waiting for printer sdw-printer"),
                mock.call("Running lpstat waiting for printer sdw-printer"),
                mock.call("Print completed"),
            ]
        )
