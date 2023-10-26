from unittest import mock

from PyQt5.QtTest import QSignalSpy

from securedrop_client.export import Export
from securedrop_client.gui.conversation.export import Device
from securedrop_client.logic import Controller
from tests import factory


class TestDevice:
    @classmethod
    def setup_class(cls):
        mock_export_service = mock.MagicMock(spec=Export)
        mock_get_file = mock.MagicMock()
        cls.mock_controller = mock.MagicMock(spec=Controller)
        cls.mock_controller.data_dir = "pretend-data-dir"
        cls.mock_controller.get_file = mock_get_file
        cls.device = Device(cls.mock_controller, mock_export_service)

    # Reset any manually-changed mock controller values before next test
    @classmethod
    def setup_method(cls):
        cls.mock_file = factory.File(source=factory.Source())
        cls.mock_controller.get_file.return_value = cls.mock_file
        cls.mock_controller.downloaded_file_exists.return_value = True

    @classmethod
    def teardown_method(cls):
        cls.mock_file = None
        cls.mock_controller.get_file.return_value = None

    def test_Device_run_printer_preflight_checks(self):
        print_preflight_check_requested_emissions = QSignalSpy(
            self.device.print_preflight_check_requested
        )

        self.device.run_printer_preflight_checks()

        assert len(print_preflight_check_requested_emissions) == 1

    def test_Device_run_print_file(self):
        # file = factory.File(source=factory.Source())
        file = self.mock_file
        print_requested_emissions = QSignalSpy(self.device.print_requested)

        self.device.print_file(file.uuid)

        assert len(print_requested_emissions) == 1

    def test_Device_print_transcript(self):
        print_requested_emissions = QSignalSpy(self.device.print_requested)

        filepath = "some/file/path"

        self.device.print_transcript(filepath)

        assert len(print_requested_emissions) == 1
        assert print_requested_emissions[0] == [["some/file/path"]]

    def test_Device_print_file_file_missing(self, mocker):
        file = self.mock_file
        self.mock_controller.downloaded_file_exists.return_value = False

        warning_logger = mocker.patch(
            "securedrop_client.gui.conversation.export.device.logger.warning"
        )

        self.device.print_file(file.uuid)

        path = str(file.location(self.mock_controller.data_dir))
        log_msg = f"Cannot find file in {path}"

        warning_logger.assert_called_once_with(log_msg)

    def test_Device_print_file_when_orig_file_already_exists(self):
        file = self.mock_file
        print_requested_emissions = QSignalSpy(self.device.print_requested)

        self.device.print_file(file.uuid)

        assert len(print_requested_emissions) == 1
        self.mock_controller.get_file.assert_called_with(file.uuid)

    def test_Device_run_export_preflight_checks(self):
        export_preflight_check_requested_emissions = QSignalSpy(
            self.device.export_preflight_check_requested
        )

        self.device.run_export_preflight_checks()

        assert len(export_preflight_check_requested_emissions) == 1

    def test_Device_export_file_to_usb_drive(self):
        file = self.mock_file
        export_requested_emissions = QSignalSpy(self.device.export_requested)
        self.device.export_file_to_usb_drive(file.uuid, "mock passphrase")

        assert len(export_requested_emissions) == 1

    def test_Device_export_file_to_usb_drive_file_missing(self, mocker):
        file = self.mock_file
        self.mock_controller.downloaded_file_exists.return_value = False

        warning_logger = mocker.patch(
            "securedrop_client.gui.conversation.export.device.logger.warning"
        )

        self.device.export_file_to_usb_drive(file.uuid, "mock passphrase")

        path = str(file.location(self.mock_controller.data_dir))
        log_msg = f"Cannot find file in {path}"
        warning_logger.assert_called_once_with(log_msg)

    def test_Device_export_file_to_usb_drive_when_orig_file_already_exists(self):
        export_requested_emissions = QSignalSpy(self.device.export_requested)
        file = self.mock_file

        self.device.export_file_to_usb_drive(file.uuid, "mock passphrase")

        assert len(export_requested_emissions) == 1
        self.mock_controller.get_file.assert_called_with(file.uuid)

    def test_Device_export_transcript(self):
        export_requested_emissions = QSignalSpy(self.device.export_requested)
        filepath = "some/file/path"

        self.device.export_transcript(filepath, "passphrase")

        assert len(export_requested_emissions) == 1
        assert export_requested_emissions[0] == [["some/file/path"], "passphrase"]

    def test_Device_export_files(self):
        export_requested_emissions = QSignalSpy(self.device.export_requested)

        filepaths = ["some/file/path", "some/other/file/path"]

        self.device.export_files(filepaths, "passphrase")

        assert len(export_requested_emissions) == 1
        assert export_requested_emissions[0] == [
            ["some/file/path", "some/other/file/path"],
            "passphrase",
        ]
