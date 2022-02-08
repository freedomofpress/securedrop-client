# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright © 2022 The Freedom of the Press Foundation.
import unittest
from unittest import mock

from PyQt5.QtWidgets import QMenu

from securedrop_client import state
from securedrop_client.gui import conversation


class TestDownloadAction(unittest.TestCase):
    def test_trigger(self):
        menu = QMenu()
        controller = mock.MagicMock()
        app_state = state.State()
        action = conversation.DownloadAction(menu, controller, app_state)

        conversation_id = state.ConversationId("some_conversation")
        app_state.selected_conversation = conversation_id

        action.trigger()

        controller.download_conversation.assert_called_once_with(conversation_id)

    def test_trigger_downloads_nothing_if_no_conversation_is_selected(self):
        menu = QMenu()
        controller = mock.MagicMock()
        app_state = state.State()
        action = conversation.DownloadAction(menu, controller, app_state)

        action.trigger()
        assert controller.download_conversation.not_called

    def test_gets_disabled_when_no_files_to_download_remain(self):
        menu = QMenu()
        controller = mock.MagicMock()
        app_state = state.State()
        action = conversation.DownloadAction(menu, controller, app_state)

        conversation_id = state.ConversationId(3)
        app_state.selected_conversation = conversation_id

        app_state.add_file(conversation_id, 5)
        app_state.file(5).is_downloaded = True

        action.setEnabled(True)  # only for extra contrast
        app_state.selected_conversation_files_changed.emit()
        assert not action.isEnabled()

    def test_gets_enabled_when_files_are_available_to_download(self):
        menu = QMenu()
        controller = mock.MagicMock()
        app_state = state.State()
        action = conversation.DownloadAction(menu, controller, app_state)

        conversation_id = state.ConversationId(3)
        app_state.selected_conversation = conversation_id

        app_state.add_file(conversation_id, 5)
        app_state.file(5).is_downloaded = False

        action.setEnabled(False)  # only for extra contrast
        app_state.selected_conversation_files_changed.emit()
        assert action.isEnabled()

    def test_gets_initially_disabled_when_file_information_is_available(self):
        menu = QMenu()
        controller = mock.MagicMock()
        app_state = state.State()

        conversation_id = state.ConversationId(3)
        app_state.selected_conversation = conversation_id
        app_state.add_file(conversation_id, 5)
        app_state.file(5).is_downloaded = True

        action = conversation.DownloadAction(menu, controller, app_state)

        assert not action.isEnabled()

    def test_gets_initially_enabled_when_file_information_is_available(self):
        menu = QMenu()
        controller = mock.MagicMock()
        app_state = state.State()

        conversation_id = state.ConversationId(3)
        app_state.selected_conversation = conversation_id
        app_state.add_file(conversation_id, 5)
        app_state.file(5).is_downloaded = False

        action = conversation.DownloadAction(menu, controller, app_state)

        assert action.isEnabled()

    def test_does_not_require_state_to_be_defined(self):
        menu = QMenu()
        controller = mock.MagicMock()
        action = conversation.DownloadAction(menu, controller, app_state=None)

        action.setEnabled(False)
        assert not action.isEnabled()

        action.setEnabled(True)
        assert action.isEnabled()

    def test_on_selected_conversation_files_changed_handles_missing_state_gracefully(
        self,
    ):
        menu = QMenu()
        controller = mock.MagicMock()
        action = conversation.DownloadAction(menu, controller, None)

        action.setEnabled(True)
        action._on_selected_conversation_files_changed()
        assert action.isEnabled()

        action.setEnabled(False)
        action._on_selected_conversation_files_changed()
        assert not action.isEnabled()
