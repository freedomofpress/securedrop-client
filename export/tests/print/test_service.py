import os
import shutil
import subprocess
import tempfile
from pathlib import Path
from unittest import mock

import pytest

from securedrop_export.archive import Archive
from securedrop_export.directory import safe_mkdir
from securedrop_export.exceptions import ExportException
from securedrop_export.print.service import Service
from securedrop_export.print.status import Status

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

    def test_printer_preflight_all_methods_called(self):
        patch_setup = mock.patch.object(self.service, "_check_printer_setup")

        mock_setup = patch_setup.start()

        self.service.printer_preflight()

        # When the client can accept new status values, we will assert that the
        # above call results in Status.PREFLIGHT_SUCCESS
        assert mock_setup.called_once()

        patch_setup.stop()

    def test_print_testpage_all_checks_called(self):
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
        ):
            self.service._print_file(target)

        assert expected.exists()
        assert mock_print_xpp.call_count == 1
        mock_print_xpp.assert_has_calls(
            [
                mock.call(
                    [
                        "xpp",
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

    @pytest.skip("Not yet implemented")
    def test__check_printer_setup(self, mocker):
        assert self.service.printer_preflight() == Status.PREFLIGHT_SUCCESS

    @pytest.skip("Not yet implemented")
    def test__check_printer_setup_error(self, ipp_usb_output, expected_status, mocker):
        with pytest.raises(ExportException) as ex:
            self.service._check_printer_setup()
        assert ex.value.sdstatus is Status.ERROR_PRINTER_NOT_FOUND

    @pytest.skip("Not yet implemented")
    def test__check_printer_setup_error_checking_printer(self, mock_output):
        with pytest.raises(ExportException) as ex:
            self.service._check_printer_setup()
        assert ex.value.sdstatus is Status.ERROR_UNKNOWN

    def test__print_test_page_calls_method(self):
        p = mock.patch.object(self.service, "_print_file")
        mock_print = p.start()

        self.service._print_test_page()
        mock_print.assert_called_once_with(Path("/usr/share/cups/data/testprint"))
        p.stop()

    def test__print_all_files(self):
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

    @mock.patch(
        "subprocess.check_output",
        side_effect=subprocess.CalledProcessError(1, "check_output"),
    )
    def test__print_file_odt_calls_libreoffice_conversion(self, mock_output):
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
                        expected_conversion_file,
                    ],
                ),
            ]
        )
        assert log.call_count == 2
        log.assert_has_calls(
            [
                mock.call("Convert to pdf for printing"),
                mock.call("Opening print dialog"),
            ]
        )

    def test__print_file_raises_if_file_not_found(self):
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
