import pytest

from securedrop_client.gui import conversation
from securedrop_client.gui.base import ModalDialog
from securedrop_client.gui.main import Window
from securedrop_client.logic import Controller
from tests import factory
from tests.helper import app  # noqa: F401


@pytest.fixture(scope="function")
def main_window(mocker, homedir):
    # Setup
    gui = Window()
    app.setActiveWindow(gui)
    gui.show()
    controller = Controller("http://localhost", gui, mocker.MagicMock(), homedir, None, proxy=False)
    controller.authenticated_user = factory.User()
    controller.qubes = False
    gui.setup(controller)

    # Create a source widget
    source_list = gui.main_view.source_list
    source = factory.Source()
    source_list.update([source])

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
    app.exit()


@pytest.fixture(scope="function")
def main_window_no_key(mocker, homedir):
    # Setup
    gui = Window()
    app.setActiveWindow(gui)
    gui.show()
    controller = Controller("http://localhost", gui, mocker.MagicMock(), homedir, None, proxy=False)
    controller.authenticated_user = factory.User()
    controller.qubes = False
    gui.setup(controller)

    # Create a source widget
    source_list = gui.main_view.source_list
    source = factory.Source(public_key=None)
    source_list.update([source])

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
    app.exit()


@pytest.fixture(scope="function")
def modal_dialog(mocker, homedir):
    gui = Window()
    gui.show()
    controller = Controller("http://localhost", gui, mocker.MagicMock(), homedir, None, proxy=False)
    controller.authenticated_user = factory.User()
    controller.qubes = False
    gui.setup(controller)
    gui.login_dialog.close()
    app.setActiveWindow(gui)
    dialog = ModalDialog()

    yield dialog

    dialog.close()
    app.exit()


@pytest.fixture(scope="function")
def print_dialog(mocker, homedir):
    gui = Window()
    gui.show()
    controller = Controller("http://localhost", gui, mocker.MagicMock(), homedir, None, proxy=False)
    controller.authenticated_user = factory.User()
    controller.qubes = False
    export_device = conversation.ExportDevice(controller)
    gui.setup(controller)
    gui.login_dialog.close()
    app.setActiveWindow(gui)
    dialog = conversation.PrintFileDialog(export_device, "file_uuid", "file_name")

    yield dialog

    dialog.close()
    app.exit()


@pytest.fixture(scope="function")
def export_dialog(mocker, homedir):
    gui = Window()
    gui.show()
    controller = Controller("http://localhost", gui, mocker.MagicMock(), homedir, None, proxy=False)
    controller.authenticated_user = factory.User()
    controller.qubes = False
    export_device = conversation.ExportDevice(controller)
    gui.setup(controller)
    gui.login_dialog.close()
    app.setActiveWindow(gui)
    dialog = conversation.ExportFileDialog(export_device, "file_uuid", "file_name")
    dialog.show()

    yield dialog

    dialog.close()
    gui.close()
