"""
Functional tests for logging into the SecureDrop client.

The tests are based upon the client testing descriptions here:
https://github.com/freedomofpress/securedrop-client/wiki/Test-plan#basic-client-testing
"""
from unittest.mock import MagicMock

from PyQt5.QtCore import Qt
from sdclientapi import AuthError, RequestTimeoutError, ServerConnectionError

from securedrop_client.app import threads
from securedrop_client.gui.auth import LoginDialog
from securedrop_client.gui.main import Window
from securedrop_client.logic import Controller


def test_login_dialog_displays_error_message_when_credentials_are_invalid(qtbot):
    dialog = LoginDialog(None)
    dialog.show()

    def dialog_is_visible():
        assert dialog.isVisible()

    def error_message_is_hidden():
        assert (
            not dialog.error_bar.error_status_bar.isVisible()
        ), "expected error message to be hidden, was visible"

    def error_message_is_empty():
        error_message = dialog.error_bar.error_status_bar.text()
        assert not error_message, f"expected error message to be empty, got '{error_message}'"

    def error_message_is_visible():
        expected_error_message = "Please enter a username, passphrase and two-factor code."
        error_message = dialog.error_bar.error_status_bar.text()
        assert (
            error_message == expected_error_message
        ), f"expected error message to be '{expected_error_message}', got '{error_message}'"

    qtbot.addWidget(dialog)
    qtbot.waitUntil(dialog_is_visible)
    qtbot.waitUntil(error_message_is_hidden)
    qtbot.waitUntil(error_message_is_empty)

    qtbot.keyClicks(dialog.username_field, "journalist")
    with qtbot.waitSignal(dialog.submit.clicked):
        qtbot.mouseClick(dialog.submit, Qt.LeftButton)

    qtbot.waitUntil(error_message_is_visible)
    dialog.close()


def test_login_dialog_is_closed_when_authentication_succeeds(qtbot, homedir):
    with threads(3) as [sync_thread, main_queue_thread, file_download_queue_thread]:
        gui = MagicMock(spec=Window)
        session = MagicMock()
        app_state = None
        no_proxy = False
        no_qubes = False
        controller = Controller(
            "http://localhost",
            gui,
            session,
            homedir,
            app_state,
            no_proxy,
            no_qubes,
            sync_thread=sync_thread,
            main_queue_thread=main_queue_thread,
            file_download_queue_thread=file_download_queue_thread,
        )
        dialog = LoginDialog(None)
        dialog.setup(controller)
        dialog.show()

        def dialog_is_visible():
            assert dialog.isVisible()

        def dialog_is_hidden():
            assert not dialog.isVisible()

        def signin_progress_is_displayed():
            submit_button_text = dialog.submit.text()
            progress_indicator = "SIGNING IN"
            assert (
                submit_button_text == progress_indicator
            ), f"expected submit button text to be '{progress_indicator}', was '{submit_button_text}'"  # noqa: E501

        def submit_credentials():
            qtbot.keyClicks(dialog.username_field, "username")
            qtbot.keyClicks(dialog.password_field, "valid passphrase")
            qtbot.keyClicks(dialog.tfa_field, "123456")

            with qtbot.waitSignal(dialog.submit.clicked):
                assert dialog.submit.text() == "SIGN IN"
                qtbot.mouseClick(dialog.submit, Qt.LeftButton)

        qtbot.addWidget(dialog)
        qtbot.waitUntil(dialog_is_visible)

        controller.call_api = lambda _, success, failure: success("authentication succeeded")
        controller.update_authenticated_user = MagicMock()

        submit_credentials()
        qtbot.waitUntil(signin_progress_is_displayed)
        qtbot.waitUntil(dialog_is_hidden)


def test_login_dialog_displays_error_message_when_authentication_fails(qtbot, homedir):

    with threads(3) as [sync_thread, main_queue_thread, file_download_queue_thread]:
        gui = MagicMock(spec=Window)
        session = MagicMock()
        app_state = None
        no_proxy = False
        no_qubes = False
        controller = Controller(
            "http://localhost",
            gui,
            session,
            homedir,
            app_state,
            no_proxy,
            no_qubes,
            sync_thread=sync_thread,
            main_queue_thread=main_queue_thread,
            file_download_queue_thread=file_download_queue_thread,
        )
        dialog = LoginDialog(None)
        dialog.setup(controller)
        dialog.show()

        def dialog_is_visible():
            assert dialog.isVisible()

        def dialog_is_hidden():
            assert not dialog.isVisible()

        def error_message_is_visible(expected_error_message):
            error_message = dialog.error_bar.error_status_bar.text()
            assert (
                error_message == expected_error_message
            ), f"expected error message to be '{expected_error_message}', got '{error_message}'"

        def generic_error_message_is_visible():
            error_message_is_visible("That didn't work. Please check everything and try again.")

        def credential_error_message_is_visible():
            error_message_is_visible(
                "Those credentials didn't work. Please try again, and \nmake sure to use a new two-factor code."  # noqa: E501
            )

        def server_error_message_is_visible():
            error_message_is_visible(
                "Could not reach the SecureDrop server. Please check your \nInternet and Tor connection and try again."  # noqa:E501
            )

        def submit_credentials():
            with qtbot.waitSignal(dialog.submit.clicked):
                assert dialog.submit.text() == "SIGN IN"
                qtbot.mouseClick(dialog.submit, Qt.LeftButton)

        qtbot.addWidget(dialog)
        qtbot.waitUntil(dialog_is_visible)

        qtbot.keyClicks(dialog.username_field, "username")
        qtbot.keyClicks(dialog.password_field, "valid passphrase")
        qtbot.keyClicks(dialog.tfa_field, "123456")

        controller.call_api = lambda _, success, failure: failure("boom")
        submit_credentials()
        assert dialog.isVisible()
        qtbot.waitUntil(generic_error_message_is_visible)

        controller.call_api = lambda _, success, failure: failure(AuthError("something happened"))
        submit_credentials()
        assert dialog.isVisible()
        qtbot.waitUntil(credential_error_message_is_visible)

        controller.call_api = lambda _, success, failure: failure(RequestTimeoutError())
        submit_credentials()
        assert dialog.isVisible()
        qtbot.waitUntil(server_error_message_is_visible)

        controller.call_api = lambda _, success, failure: failure(ServerConnectionError())
        submit_credentials()
        assert dialog.isVisible()
        qtbot.waitUntil(server_error_message_is_visible)
