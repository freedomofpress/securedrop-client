import pytest
from PyQt5.QtWidgets import QApplication

from securedrop_client.app import threads
from securedrop_client.export import Export
from securedrop_client.export_status import ExportStatus
from securedrop_client.gui import conversation
from securedrop_client.gui.base import ModalDialog
from securedrop_client.gui.main import Window
from securedrop_client.logic import Controller
from tests import factory


@pytest.fixture()
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


@pytest.fixture()
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


@pytest.fixture()
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


@pytest.fixture()
def mock_export(mocker):
    export = Export()

    """An export that assumes the Qubes RPC calls are successful and skips them."""
    export.run_export_preflight_checks = lambda: export.export_state_changed.emit(
        ExportStatus.DEVICE_LOCKED
    )
    export.export = lambda paths, passphrase: export.export_state_changed.emit(
        ExportStatus.SUCCESS_EXPORT
    )
    export.run_printer_preflight_checks = lambda: export.export_state_changed.emit(
        ExportStatus.PRINT_PREFLIGHT_SUCCESS
    )
    export.print = lambda paths: export.export_state_changed.emit(ExportStatus.PRINT_SUCCESS)
    return export


@pytest.fixture()
def print_dialog(mocker, homedir, mock_export):
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
        dialog = conversation.PrintDialog(mock_export, "file_name", ["/mock/export/file"])

        yield dialog

        dialog.close()
    gui.close()
    app.exit()


@pytest.fixture()
def export_file_wizard(mocker, homedir, mock_export):
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
        dialog = conversation.ExportWizard(mock_export, "file_name", ["/mock/export/filepath"])
        dialog.show()

        yield dialog

        dialog.close()
    gui.close()
    app.exit()
