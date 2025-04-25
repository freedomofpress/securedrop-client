import locale
import unittest
from contextlib import contextmanager
from tempfile import TemporaryDirectory
from unittest import mock
from unittest.mock import MagicMock, Mock, patch

from PyQt5.QtCore import QTimer
from PyQt5.QtWidgets import QDialog, QMenu

from securedrop_client import state
from securedrop_client.db import File, Source
from securedrop_client.gui.actions import (
    DeleteConversationAction,
    DeleteSourceAction,
    DownloadConversation,
    ExportConversationAction,
    ExportConversationTranscriptAction,
    PrintConversationAction,
)
from securedrop_client.gui.widgets import ConversationView, FileWidget
from securedrop_client.logic import Controller
from tests import factory


class DeleteConversationActionTest(unittest.TestCase):
    def setUp(self):
        self._source = factory.Source()
        _menu = QMenu()
        self._controller = MagicMock(Controller, api=True)
        self._app_state = MagicMock(
            state.State, selected_conversation=state.ConversationId("some_conversation")
        )
        self._dialog = QDialog()

        def _dialog_constructor(source: Source) -> QDialog:
            return self._dialog

        self.action = DeleteConversationAction(
            self._source, _menu, self._controller, _dialog_constructor, self._app_state
        )

    def test_deletes_conversation_when_dialog_accepted(self):
        # Accept the confirmation dialog from a separate thread.
        QTimer.singleShot(10, self._dialog.accept)

        self.action.trigger()

        (self._controller.delete_conversation.assert_called_once_with(self._source),)
        self._app_state.remove_conversation_files.assert_called_once_with(
            state.ConversationId("some_conversation")
        )

    def test_does_not_delete_conversation_when_dialog_rejected(self):
        # Reject the confirmation dialog from a separate thread.
        QTimer.singleShot(10, self._dialog.reject)

        self.action.trigger()

        assert not self._controller.delete_conversation.called
        assert not self._app_state.remove_conversation_files.called

    def test_requires_authenticated_journalist(self):
        controller = mock.MagicMock(Controller, api=None)  # no authenticated user
        self.action.controller = controller

        confirmation_dialog = mock.MagicMock()
        self.action._confirmation_dialog = confirmation_dialog

        self.action.trigger()

        assert not confirmation_dialog.exec.called
        assert not controller.delete_conversation.called
        controller.on_action_requiring_login.assert_called_once()

    def test_deletes_nothing_if_no_conversation_is_selected(self):
        self._app_state.selected_conversation = None

        # Accept the confirmation dialog from a separate thread.
        QTimer.singleShot(10, self._dialog.accept)

        self.action.trigger()

        assert not self._controller.delete_conversation.called
        assert not self._app_state.remove_conversation_files.called


class DeleteSourceActionTest(unittest.TestCase):
    def setUp(self):
        self._source = factory.Source()
        _menu = QMenu()
        self._controller = MagicMock(Controller, api=True)
        self._dialog = QDialog()

        def _dialog_constructor(source: Source, source_total: int) -> QDialog:
            return self._dialog

        self.action = DeleteSourceAction(self._source, _menu, self._controller, _dialog_constructor)

    def test_deletes_source_when_dialog_accepted(self):
        # Accept the confirmation dialog from a separate thread.
        QTimer.singleShot(10, self._dialog.accept)

        self.action.trigger()

        self._controller.delete_sources.assert_called_once()
        assert self._source in self._controller.delete_sources.call_args[0][0], (
            self._controller.delete_sources.call_args[0][0]
        )

    def test_does_not_delete_source_when_dialog_rejected(self):
        # Reject the confirmation dialog from a separate thread.
        QTimer.singleShot(10, self._dialog.reject)

        self.action.trigger()

        assert not self._controller.delete_sources.called

    def test_requires_authenticated_journalist(self):
        controller = mock.MagicMock(Controller, api=None)  # no authenticated user
        self.action.controller = controller

        confirmation_dialog = mock.MagicMock()
        self.action._confirmation_dialog = confirmation_dialog

        self.action.trigger()

        assert not confirmation_dialog.exec.called
        assert not controller.delete_sources.called
        controller.on_action_requiring_login.assert_called_once()


class TestDownloadConversation(unittest.TestCase):
    def test_trigger(self):
        menu = QMenu()
        controller = MagicMock(Controller, api=True)
        file = factory.File(is_downloaded=False)
        progress_proxy = MagicMock()
        progress = MagicMock(proxy=lambda: progress_proxy)

        conversation_view = MagicMock(
            ConversationView,
            current_messages={
                file.uuid: MagicMock(FileWidget, file=file, download_progress=progress),
            },
        )

        action = DownloadConversation(menu, controller, conversation_view)

        action.trigger()
        controller.on_submission_download.assert_called_once_with(File, file.uuid, progress_proxy)

    def test_requires_authenticated_journalist(self):
        menu = QMenu()
        controller = mock.MagicMock(Controller, api=None)  # no authenticated user
        action = DownloadConversation(menu, controller, MagicMock())

        action.trigger()

        assert not controller.on_submission_download.called
        controller.on_action_requiring_login.assert_called_once()

    def test_gets_disabled_when_no_files_to_download_remain(self):
        menu = QMenu()
        controller = MagicMock(Controller, api=True)
        file = factory.File(is_downloaded=True)
        conversation_view = MagicMock(
            ConversationView,
            current_messages={
                file.uuid: MagicMock(FileWidget, file=file),
            },
        )

        action = DownloadConversation(menu, controller, conversation_view)
        assert action.isEnabled(), "always enabled when in background"

        assert not action.has_downloadable_files()
        action.on_about_to_show()
        assert not action.isEnabled(), "state changed after QMenu opened"

    def test_gets_enabled_when_files_are_available_to_download(self):
        menu = QMenu()
        controller = MagicMock(Controller, api=True)
        file = factory.File(is_downloaded=False)
        conversation_view = MagicMock(
            ConversationView,
            current_messages={
                file.uuid: MagicMock(FileWidget, file=file),
            },
        )

        action = DownloadConversation(menu, controller, conversation_view)
        assert action.isEnabled(), "always enabled when in background"

        assert action.has_downloadable_files()
        action.on_about_to_show()
        assert action.isEnabled(), "state didn't change after QMenu opened"


@contextmanager
def managed_locale():
    """Ensure that the curent locale is restored when the context expires."""
    loc, enc = locale.getlocale()
    yield loc, enc
    locale.setlocale(locale.LC_ALL, (loc, enc))


class TestPrintConversationAction(unittest.TestCase):
    @patch("securedrop_client.gui.actions.PrintDialog")
    def test_trigger(self, _):
        with managed_locale():
            locale.setlocale(locale.LC_ALL, ("en_US", "latin-1"))

            with TemporaryDirectory() as tmp_dir:
                menu = QMenu()
                controller = MagicMock(Controller, api=True, data_dir=tmp_dir)
                source = MagicMock(Source, journalist_filename="mysterious-writer")
                action = PrintConversationAction(menu, controller, source)
                with patch("securedrop_client.gui.actions.ConversationTranscript") as transcript:
                    transcript.return_value.__str__ = Mock(
                        return_value="☠ A string with unicode characters."
                    )

                    action.trigger()

                    assert True  # the transcript is written without errors


class TestExportConversationTranscriptAction(unittest.TestCase):
    @patch("securedrop_client.gui.actions.ExportWizard")
    def test_trigger(self, _):
        with managed_locale():
            locale.setlocale(locale.LC_ALL, ("en_US", "latin-1"))

            with TemporaryDirectory() as tmp_dir:
                menu = QMenu()
                controller = MagicMock(Controller, api=True, data_dir=tmp_dir)
                source = MagicMock(Source, journalist_filename="mysterious-writer")
                action = ExportConversationTranscriptAction(menu, controller, source)
                with patch("securedrop_client.gui.actions.ConversationTranscript") as transcript:
                    transcript.return_value.__str__ = Mock(
                        return_value="☠ A string with unicode characters."
                    )

                    action.trigger()

                    assert True  # the transcript is written without errors


class TestExportConversationAction(unittest.TestCase):
    @patch("securedrop_client.gui.actions.ExportWizard")
    def test_trigger(self, _):
        with managed_locale():
            locale.setlocale(locale.LC_ALL, ("en_US", "latin-1"))

            with TemporaryDirectory() as tmp_dir:
                menu = QMenu()
                controller = MagicMock(Controller, api=True, data_dir=tmp_dir)
                source = MagicMock(Source, journalist_filename="mysterious-writer")
                app_state = MagicMock(
                    state.State,
                    selected_conversation=state.ConversationId("some_conversation"),
                    selected_conversation_has_downloadable_files=False,
                )
                action = ExportConversationAction(menu, controller, source, app_state)
                with patch("securedrop_client.gui.actions.ConversationTranscript") as transcript:
                    transcript.return_value.__str__ = Mock(
                        return_value="☠ A string with unicode characters."
                    )

                    action.trigger()

                    assert True  # the transcript is written without errors
