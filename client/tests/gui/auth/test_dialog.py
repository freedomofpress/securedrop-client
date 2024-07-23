import pytest

from securedrop_client.gui.auth import LoginDialog
from tests.helper import app  # noqa: F401


@pytest.mark.parametrize("lang", ["es"], indirect=True)
def test_LoginDialog_translated(lang):
    """
    The LoginDialog is translated when a valid $LANG is set.

    We use LANG=es because Spanish is reliably translated, and the translation
    of "Username" is unlikely to drift.  These values could be factored out into
    constants or even read (via polib) from the gettext catalogs under
    "securedrop_client/locale/", but the complication (never mind the extra
    dependency) doesn't seem worthwhile for a few tests.
    """
    ld = LoginDialog(None)
    assert ld.username_label.text() == "Nombre de Usuario"  # expected translation


@pytest.mark.parametrize("lang", ["foo"], indirect=True)
def test_LoginDialog_not_translated_with_invalid_lang(lang):
    """
    The LoginDialog falls back to source (English) strings when an invalid $LANG
    is set.  See test_LoginDialog_translated() above for commentary.
    """
    ld = LoginDialog(None)
    assert ld.username_label.text() == "Username"  # expected source string


def test_LoginDialog_setup(mocker, i18n):
    """
    The LoginView is correctly initialised.
    """
    mock_controller = mocker.MagicMock()
    ld = LoginDialog(None)
    ld.offline_mode = mocker.MagicMock()

    ld.setup(mock_controller)

    assert ld.controller == mock_controller
    ld.offline_mode.clicked.connect.assert_called_once_with(ld.controller.login_offline_mode)


def test_LoginDialog_reset(mocker):
    """
    Ensure the state of the login view is returned to the correct state.
    """
    mock_controller = mocker.MagicMock()

    ld = LoginDialog(None)
    ld.setup(mock_controller)
    ld.username_field = mocker.MagicMock()
    ld.password_field = mocker.MagicMock()
    ld.tfa_field = mocker.MagicMock()
    ld.setDisabled = mocker.MagicMock()
    ld.error_bar = mocker.MagicMock()

    ld.reset()

    ld.username_field.setText.assert_called_once_with("")
    ld.password_field.setText.assert_called_once_with("")
    ld.tfa_field.setText.assert_called_once_with("")
    ld.setDisabled.assert_called_once_with(False)
    ld.error_bar.clear_message.assert_called_once_with()


def test_LoginDialog_error(mocker, i18n):
    """
    Any error message passed in is assigned as the text for the error label.
    """
    mock_controller = mocker.MagicMock()
    ld = LoginDialog(None)
    ld.setup(mock_controller)
    ld.error_bar = mocker.MagicMock()
    ld.error("foo")
    ld.error_bar.set_message.assert_called_once_with("foo")


def test_LoginDialog_validate_no_input(mocker):
    """
    If the user doesn't provide input, tell them and give guidance.
    """
    mock_controller = mocker.MagicMock()

    ld = LoginDialog(None)
    ld.setup(mock_controller)
    ld.username_field.text = mocker.MagicMock(return_value="")
    ld.password_field.text = mocker.MagicMock(return_value="")
    ld.tfa_field.text = mocker.MagicMock(return_value="")
    ld.setDisabled = mocker.MagicMock()
    ld.error = mocker.MagicMock()

    ld.validate()

    assert ld.setDisabled.call_count == 2
    assert ld.error.call_count == 1


def test_LoginDialog_validate_input_non_numeric_2fa(mocker):
    """
    If the user doesn't provide numeric 2fa input, tell them and give
    guidance.
    """
    mock_controller = mocker.MagicMock()

    ld = LoginDialog(None)
    ld.setup(mock_controller)
    ld.username_field.text = mocker.MagicMock(return_value="foo")
    ld.password_field.text = mocker.MagicMock(return_value="nicelongpassword")
    ld.tfa_field.text = mocker.MagicMock(return_value="baz")
    ld.setDisabled = mocker.MagicMock()
    ld.error = mocker.MagicMock()

    ld.validate()

    assert ld.setDisabled.call_count == 2
    assert ld.error.call_count == 1
    assert mock_controller.login.call_count == 0


def test_LoginDialog_validate_too_short_username(mocker):
    """
    If the username is too small, we show an informative error message.
    """
    mock_controller = mocker.MagicMock()

    ld = LoginDialog(None)
    ld.setup(mock_controller)
    ld.username_field.text = mocker.MagicMock(return_value="he")
    ld.password_field.text = mocker.MagicMock(return_value="nicelongpassword")
    ld.tfa_field.text = mocker.MagicMock(return_value="123456")
    ld.setDisabled = mocker.MagicMock()
    ld.error = mocker.MagicMock()

    ld.validate()

    assert ld.setDisabled.call_count == 2
    assert ld.error.call_count == 1
    assert mock_controller.login.call_count == 0


def test_LoginDialog_validate_too_short_password(mocker):
    """
    If the password is too small, we show an informative error message.
    """
    mock_controller = mocker.MagicMock()

    ld = LoginDialog(None)
    ld.setup(mock_controller)
    ld.username_field.text = mocker.MagicMock(return_value="foo")
    ld.password_field.text = mocker.MagicMock(return_value="bar")
    ld.tfa_field.text = mocker.MagicMock(return_value="123456")
    ld.setDisabled = mocker.MagicMock()
    ld.error = mocker.MagicMock()

    ld.validate()

    assert ld.setDisabled.call_count == 2
    assert ld.error.call_count == 1
    assert mock_controller.login.call_count == 0


def test_LoginDialog_validate_too_long_password(mocker):
    """
    If the password is too long, we show an informative error message.
    """
    mock_controller = mocker.MagicMock()
    ld = LoginDialog(None)
    ld.setup(mock_controller)

    max_password_len = 128
    too_long_password = "a" * (max_password_len + 1)

    ld.username_field.text = mocker.MagicMock(return_value="foo")
    ld.password_field.text = mocker.MagicMock(return_value=too_long_password)
    ld.tfa_field.text = mocker.MagicMock(return_value="123456")
    ld.setDisabled = mocker.MagicMock()
    ld.error = mocker.MagicMock()

    ld.validate()

    assert ld.setDisabled.call_count == 2
    assert ld.error.call_count == 1
    assert mock_controller.login.call_count == 0


def test_LoginDialog_validate_input_ok(mocker):
    """
    Valid input from the user causes a call to the controller's login method.
    """
    mock_controller = mocker.MagicMock()

    ld = LoginDialog(None)
    ld.setup(mock_controller)
    ld.username_field.text = mocker.MagicMock(return_value="foo")
    ld.password_field.text = mocker.MagicMock(return_value="nicelongpassword")
    ld.tfa_field.text = mocker.MagicMock(return_value="123456")
    ld.setDisabled = mocker.MagicMock()
    ld.error = mocker.MagicMock()

    ld.validate()

    assert ld.setDisabled.call_count == 1
    assert ld.error.call_count == 0
    mock_controller.login.assert_called_once_with("foo", "nicelongpassword", "123456")
