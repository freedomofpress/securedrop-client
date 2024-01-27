import pytest
from PyQt5.QtWidgets import QApplication

from securedrop_client.app import threads
from securedrop_client.export_status import ExportStatus
from securedrop_client.gui import conversation
from securedrop_client.gui.base import ModalDialog
from securedrop_client.gui.conversation.export import Export
from securedrop_client.gui.main import Window
from securedrop_client.logic import Controller
from tests import factory


@pytest.fixture(scope="function")
def main_window(mocker, homedir):
    # Setup
    app = QApplication([])
    gui = Window()
    app.setActiveWindow(gui)
    gui.show()
    with threads(3) as [sync_thread, main_queue_thread, file_download_thread]:
        controller = Controller(
            "http://localhost",
            gui,
            mocker.MagicMock(),
            homedir,
            None,
            sync_thread=sync_thread,
            main_queue_thread=main_queue_thread,
            file_download_queue_thread=file_download_thread,
            proxy=False,
        )
        controller.authenticated_user = factory.User()
        controller.qubes = False
        gui.setup(controller)

        # Create a source widget
        source_list = gui.main_view.source_list
        source = factory.Source()
        source_list.update_sources([source])

        # Create a file widget, message widget, and reply widget
        mocker.patch("securedrop_client.gui.widgets.humanize_filesize", return_value="100")
        mocker.patch(
            "securedrop_client.gui.base.SecureQLabel.get_elided_text",
            return_value="1-yellow-doc.gz.gpg",
        )
        source.collection.append(
            [
                factory.File(source=source, filename="1-yellow-doc.gz.gpg"),
                factory.Message(source=source, filename="2-yellow-msg.gpg"),
                factory.Reply(source=source, filename="3-yellow-reply.gpg"),
            ]
        )
        source_list.setCurrentItem(source_list.item(0))
        gui.main_view.on_source_changed()

        yield gui

        # Teardown
        gui.login_dialog.close()
    gui.close()
    app.exit()


@pytest.fixture(scope="function")
def main_window_no_key(mocker, homedir):
    # Setup
    app = QApplication([])
    gui = Window()
    app.setActiveWindow(gui)
    gui.show()
    with threads(3) as [sync_thread, main_queue_thread, file_download_thread]:
        controller = Controller(
            "http://localhost",
            gui,
            mocker.MagicMock(),
            homedir,
            None,
            sync_thread=sync_thread,
            main_queue_thread=main_queue_thread,
            file_download_queue_thread=file_download_thread,
            proxy=False,
        )
        controller.authenticated_user = factory.User()
        controller.qubes = False
        gui.setup(controller)

        # Create a source widget
        source_list = gui.main_view.source_list
        source = factory.Source(public_key=None)
        source_list.update_sources([source])

        # Create a file widget, message widget, and reply widget
        mocker.patch("securedrop_client.gui.widgets.humanize_filesize", return_value="100")
        mocker.patch(
            "securedrop_client.gui.base.SecureQLabel.get_elided_text",
            return_value="1-yellow-doc.gz.gpg",
        )
        source.collection.append(
            [
                factory.File(source=source, filename="1-yellow-doc.gz.gpg"),
                factory.Message(source=source, filename="2-yellow-msg.gpg"),
                factory.Reply(source=source, filename="3-yellow-reply.gpg"),
            ]
        )
        source_list.setCurrentItem(source_list.item(0))
        gui.main_view.on_source_changed()

        yield gui

        # Teardown
        gui.login_dialog.close()
    gui.close()
    app.exit()


@pytest.fixture(scope="function")
def modal_dialog(mocker, homedir):
    app = QApplication([])
    gui = Window()
    app.setActiveWindow(gui)
    gui.show()
    with threads(3) as [sync_thread, main_queue_thread, file_download_thread]:
        controller = Controller(
            "http://localhost",
            gui,
            mocker.MagicMock(),
            homedir,
            None,
            sync_thread=sync_thread,
            main_queue_thread=main_queue_thread,
            file_download_queue_thread=file_download_thread,
            proxy=False,
        )
        controller.authenticated_user = factory.User()
        controller.qubes = False
        gui.setup(controller)
        gui.login_dialog.close()
        dialog = ModalDialog()

        yield dialog

        dialog.close()
    gui.close()
    app.exit()


@pytest.fixture(scope="function")
def mock_export(mocker):
    device = Export()

    """A export that assumes the Qubes RPC calls are successful and skips them."""
    device.run_preflight_checks = lambda: ExportStatus.DEVICE_LOCKED
    device.send_file_to_usb_device = lambda paths, passphrase: ExportStatus.SUCCESS_EXPORT
    device.run_printer_preflight = lambda: ExportStatus.PRINT_PREFLIGHT_SUCCESS
    device.run_print = lambda paths: ExportStatus.PRINT_SUCCESS
    return device


@pytest.fixture(scope="function")
def print_dialog(mocker, homedir):
    mocker.patch("securedrop_client.export.Export", return_value=mock_export)
    app = QApplication([])
    gui = Window()
    app.setActiveWindow(gui)
    gui.show()
    with threads(3) as [sync_thread, main_queue_thread, file_download_thread]:
        controller = Controller(
            "http://localhost",
            gui,
            mocker.MagicMock(),
            homedir,
            None,
            sync_thread=sync_thread,
            main_queue_thread=main_queue_thread,
            file_download_queue_thread=file_download_thread,
            proxy=False,
        )
        controller = Controller(
            "http://localhost", gui, mocker.MagicMock(), homedir, None, proxy=False
        )
        controller.authenticated_user = factory.User()
        controller.qubes = False
        gui.setup(controller)
        gui.login_dialog.close()
        export_device = conversation.ExportDevice()
        dialog = conversation.PrintFileDialog(export_device, "file_name", ["/mock/export/file"])

        yield dialog

        dialog.close()
    gui.close()
    app.exit()


@pytest.fixture(scope="function")
def export_file_dialog(mocker, homedir):
    mocker.patch("securedrop_client.export.Export", return_value=mock_export)
    app = QApplication([])
    gui = Window()
    app.setActiveWindow(gui)
    gui.show()
    with threads(3) as [sync_thread, main_queue_thread, file_download_thread]:
        controller = Controller(
            "http://localhost",
            gui,
            mocker.MagicMock(),
            homedir,
            None,
            sync_thread=sync_thread,
            main_queue_thread=main_queue_thread,
            file_download_queue_thread=file_download_thread,
            proxy=False,
        )
        controller.authenticated_user = factory.User()
        controller.qubes = False
        gui.setup(controller)
        gui.login_dialog.close()
        export_device = conversation.ExportDevice()
        dialog = conversation.ExportFileDialog(
            export_device, "file_name", ["/mock/export/filepath"]
        )
        dialog.show()

        yield dialog

        dialog.close()
    gui.close()
    app.exit()
