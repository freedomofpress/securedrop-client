from gettext import gettext as _

from PyQt5.QtWidgets import QApplication

from securedrop_client.gui.source import DeleteSourceDialog
from tests import factory

app = QApplication([])


def test_DeleteSourceDialog_init(mocker, source):
    mock_controller = mocker.MagicMock()
    DeleteSourceDialog(source["source"], mock_controller)


def test_DeleteSourceDialog_cancel(mocker, source):
    source = source["source"]  # to get the Source object

    mock_controller = mocker.MagicMock()
    delete_source_dialog = DeleteSourceDialog(source, mock_controller)
    delete_source_dialog.cancel_button.click()
    mock_controller.delete_source.assert_not_called()


def test_DeleteSourceDialog_continue(mocker, source, session):
    source = source["source"]  # to get the Source object

    mock_controller = mocker.MagicMock()
    delete_source_dialog = DeleteSourceDialog(source, mock_controller)
    delete_source_dialog.continue_button.click()
    mock_controller.delete_source.assert_called_once_with(source)


def test_DeleteSourceDialog_make_body_text(mocker, source, session):
    source = source["source"]  # to get the Source object
    file_ = factory.File(source=source)
    session.add(file_)
    message = factory.Message(source=source)
    session.add(message)
    message = factory.Message(source=source)
    session.add(message)
    reply = factory.Reply(source=source)
    session.add(reply)
    session.commit()

    mock_controller = mocker.MagicMock()

    delete_source_message_box = DeleteSourceDialog(source, mock_controller)

    message = delete_source_message_box.make_body_text()

    expected_message = "".join(
        (
            "<style>",
            "p {{white-space: nowrap;}}",
            "</style>",
            "<p><b>",
            _("When the entire account for a source is deleted:"),
            "</b></p>",
            "<p><b>\u2219</b>&nbsp;",
            _("The source will not be able to log in with their codename again."),
            "</p>",
            "<p><b>\u2219</b>&nbsp;",
            _("Your organization will not be able to send them replies."),
            "</p>",
            "<p><b>\u2219</b>&nbsp;",
            _("All files and messages from that source will also be destroyed."),
            "</p>",
            "<p>&nbsp;</p>",
        )
    ).format(source=source.journalist_designation)
    assert message == expected_message
