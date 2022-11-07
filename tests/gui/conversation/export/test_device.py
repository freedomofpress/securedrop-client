import os

from PyQt5.QtTest import QSignalSpy

from securedrop_client import export
from securedrop_client.app import threads
from securedrop_client.gui.conversation.export import Device
from securedrop_client.gui.main import Window
from securedrop_client.logic import Controller
from tests import factory


def no_session():
    pass


def test_Device_run_printer_preflight_checks(homedir, mocker, source):
    gui = mocker.MagicMock(spec=Window)
    with threads(3) as [sync_thread, main_queue_thread, file_download_queue_thread]:
        controller = Controller(
            "http://localhost",
            gui,
            no_session,
            homedir,
            None,
            sync_thread=sync_thread,
            main_queue_thread=main_queue_thread,
            file_download_queue_thread=file_download_queue_thread,
        )
        export_service = export.Service()
        device = Device(controller, export_service)
        print_preflight_check_requested_emissions = QSignalSpy(
            device.print_preflight_check_requested
        )

        device.run_printer_preflight_checks()

        assert len(print_preflight_check_requested_emissions) == 1


def test_Device_run_print_file(mocker, homedir):
    gui = mocker.MagicMock(spec=Window)
    with threads(3) as [sync_thread, main_queue_thread, file_download_queue_thread]:
        controller = Controller(
            "http://localhost",
            gui,
            no_session,
            homedir,
            None,
            sync_thread=sync_thread,
            main_queue_thread=main_queue_thread,
            file_download_queue_thread=file_download_queue_thread,
        )
        export_service = export.Service()
        device = Device(controller, export_service)
        print_requested_emissions = QSignalSpy(device.print_requested)
        file = factory.File(source=factory.Source())
        mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)

        filepath = file.location(controller.data_dir)
        os.makedirs(os.path.dirname(filepath), mode=0o700, exist_ok=True)
        with open(filepath, "w"):
            pass

        device.print_file(file.uuid)

        assert len(print_requested_emissions) == 1


def test_Device_print_file_file_missing(homedir, mocker, session):
    """
    If the file is missing from the data dir, is_downloaded should be set to False and the failure
    should be communicated to the user.
    """
    gui = mocker.MagicMock()
    with threads(3) as [sync_thread, main_queue_thread, file_download_queue_thread]:
        controller = Controller(
            "http://localhost",
            gui,
            session,
            homedir,
            None,
            sync_thread=sync_thread,
            main_queue_thread=main_queue_thread,
            file_download_queue_thread=file_download_queue_thread,
        )
        export_service = export.Service()
        device = Device(controller, export_service)
        file = factory.File(source=factory.Source())
        mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)
        warning_logger = mocker.patch("securedrop_client.logic.logger.warning")

        device.print_file(file.uuid)

        log_msg = "Cannot find file in {}. File does not exist.".format(
            os.path.dirname(file.filename)
        )
        warning_logger.assert_called_once_with(log_msg)


def test_Device_print_file_when_orig_file_already_exists(homedir, config, mocker, source):
    """
    The signal `print_requested` should still be emitted if the original file already exists.
    """
    gui = mocker.MagicMock(spec=Window)
    with threads(3) as [sync_thread, main_queue_thread, file_download_queue_thread]:
        controller = Controller(
            "http://localhost",
            gui,
            no_session,
            homedir,
            None,
            sync_thread=sync_thread,
            main_queue_thread=main_queue_thread,
            file_download_queue_thread=file_download_queue_thread,
        )
        export_service = export.Service()
        device = Device(controller, export_service)
        file = factory.File(source=factory.Source())
        print_requested_emissions = QSignalSpy(device.print_requested)
        mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)
        mocker.patch("os.path.exists", return_value=True)

        device.print_file(file.uuid)

        assert len(print_requested_emissions) == 1
        controller.get_file.assert_called_with(file.uuid)


def test_Device_run_export_preflight_checks(homedir, mocker, source):
    gui = mocker.MagicMock(spec=Window)
    with threads(3) as [sync_thread, main_queue_thread, file_download_queue_thread]:
        controller = Controller(
            "http://localhost",
            gui,
            no_session,
            homedir,
            None,
            sync_thread=sync_thread,
            main_queue_thread=main_queue_thread,
            file_download_queue_thread=file_download_queue_thread,
        )
        device = Device(controller, mocker.MagicMock(spec=export.Service))
        export_preflight_check_requested_emissions = QSignalSpy(
            device.export_preflight_check_requested
        )
        file = factory.File(source=source["source"])
        mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)

        device.run_export_preflight_checks()

        assert len(export_preflight_check_requested_emissions) == 1


def test_Device_export_file_to_usb_drive(homedir, mocker):
    """
    The signal `export_requested` should be emitted during export_file_to_usb_drive.
    """
    gui = mocker.MagicMock(spec=Window)
    with threads(3) as [sync_thread, main_queue_thread, file_download_queue_thread]:
        controller = Controller(
            "http://localhost",
            gui,
            no_session,
            homedir,
            None,
            sync_thread=sync_thread,
            main_queue_thread=main_queue_thread,
            file_download_queue_thread=file_download_queue_thread,
        )
        export_service = export.Service()
        device = Device(controller, export_service)
        export_requested_emissions = QSignalSpy(device.export_requested)
        file = factory.File(source=factory.Source())
        mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)

        filepath = file.location(controller.data_dir)
        os.makedirs(os.path.dirname(filepath), mode=0o700, exist_ok=True)
        with open(filepath, "w"):
            pass

        device.export_file_to_usb_drive(file.uuid, "mock passphrase")

        assert len(export_requested_emissions) == 1


def test_Device_export_file_to_usb_drive_file_missing(homedir, mocker, session):
    """
    If the file is missing from the data dir, is_downloaded should be set to False and the failure
    should be communicated to the user.
    """
    gui = mocker.MagicMock(spec=Window)
    with threads(3) as [sync_thread, main_queue_thread, file_download_queue_thread]:
        controller = Controller(
            "http://localhost",
            gui,
            session,
            homedir,
            None,
            sync_thread=sync_thread,
            main_queue_thread=main_queue_thread,
            file_download_queue_thread=file_download_queue_thread,
        )
        export_service = export.Service()
        device = Device(controller, export_service)
        file = factory.File(source=factory.Source())
        mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)
        warning_logger = mocker.patch("securedrop_client.logic.logger.warning")

        device.export_file_to_usb_drive(file.uuid, "mock passphrase")

        log_msg = "Cannot find file in {}. File does not exist.".format(
            os.path.dirname(file.filename)
        )
        warning_logger.assert_called_once_with(log_msg)


def test_Device_export_file_to_usb_drive_when_orig_file_already_exists(
    homedir, config, mocker, source
):
    """
    The signal `export_requested` should still be emitted if the original file already exists.
    """
    gui = mocker.MagicMock(spec=Window)
    with threads(3) as [sync_thread, main_queue_thread, file_download_queue_thread]:
        controller = Controller(
            "http://localhost",
            gui,
            no_session,
            homedir,
            None,
            sync_thread=sync_thread,
            main_queue_thread=main_queue_thread,
            file_download_queue_thread=file_download_queue_thread,
        )
        export_service = export.Service()
        device = Device(controller, export_service)
        export_requested_emissions = QSignalSpy(device.export_requested)
        file = factory.File(source=factory.Source())
        mocker.patch("securedrop_client.logic.Controller.get_file", return_value=file)
        mocker.patch("os.path.exists", return_value=True)

        device.export_file_to_usb_drive(file.uuid, "mock passphrase")

        assert len(export_requested_emissions) == 1
        controller.get_file.assert_called_with(file.uuid)
