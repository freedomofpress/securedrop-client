"""
Tests for the gui helper functions in __init__.py
"""
from PyQt5.QtCore import QSize, Qt

from securedrop_client.gui.base import SecureQLabel, SvgLabel, SvgPushButton, SvgToggleButton
from tests.helper import app  # noqa: F401


def test_SvgToggleButton_init(mocker):
    """
    Ensure SvgToggleButton is checkable, which allows it to be a toggle button and that the expected
    methods are called correctly to set the icon and size.
    """
    svg_size = QSize(1, 1)
    icon = mocker.MagicMock()
    load_icon_fn = mocker.patch("securedrop_client.gui.base.misc.load_icon", return_value=icon)
    setIcon_fn = mocker.patch("securedrop_client.gui.base.SvgToggleButton.setIcon")
    setIconSize_fn = mocker.patch("securedrop_client.gui.base.SvgToggleButton.setIconSize")

    stb = SvgToggleButton(on="mock_on", off="mock_off", svg_size=svg_size)

    assert stb.isCheckable() is True
    load_icon_fn.assert_called_once_with(normal="mock_on", normal_off="mock_off")
    setIcon_fn.assert_called_once_with(icon)
    setIconSize_fn.assert_called_once_with(svg_size)


def test_SvgToggleButton_toggle(mocker):
    """
    Make sure we're not calling this a toggle button for no reason.
    """
    stb = SvgToggleButton(on="mock_on", off="mock_off")
    stb.toggle()
    assert stb.isChecked() is True
    stb.toggle()
    assert stb.isChecked() is False
    stb.toggle()
    assert stb.isChecked() is True


def test_SvgToggleButton_set_icon(mocker):
    """
    Ensure set_icon loads and sets the icon.
    """
    setIcon_fn = mocker.patch("securedrop_client.gui.base.SvgToggleButton.setIcon")
    icon = mocker.MagicMock()
    load_icon_fn = mocker.patch("securedrop_client.gui.base.misc.load_icon", return_value=icon)
    stb = SvgToggleButton(on="mock_on", off="mock_off")

    stb.set_icon(on="mock_on", off="mock_off")

    load_icon_fn.assert_called_with(normal="mock_on", normal_off="mock_off")
    setIcon_fn.assert_called_with(icon)
    assert stb._icon == icon


def test_SvgPushButton_init(mocker):
    """
    Ensure SvgPushButton calls the expected methods correctly to set the icon and size.
    """
    svg_size = QSize(1, 1)
    icon = mocker.MagicMock()
    load_icon_fn = mocker.patch("securedrop_client.gui.base.misc.load_icon", return_value=icon)
    setIcon_fn = mocker.patch("securedrop_client.gui.base.SvgPushButton.setIcon")
    setIconSize_fn = mocker.patch("securedrop_client.gui.base.SvgPushButton.setIconSize")

    spb = SvgPushButton(
        normal="mock1", disabled="mock2", active="mock3", selected="mock4", svg_size=svg_size
    )

    assert spb.isCheckable() is False
    load_icon_fn.assert_called_once_with(
        normal="mock1", disabled="mock2", active="mock3", selected="mock4", disabled_off="mock2"
    )
    setIcon_fn.assert_called_once_with(icon)
    setIconSize_fn.assert_called_once_with(svg_size)


def test_SvgLabel_init(mocker):
    """
    Ensure SvgLabel calls the expected methods correctly to set the icon and size.
    """
    svg_size = QSize(1, 1)
    svg = mocker.MagicMock()
    load_svg_fn = mocker.patch("securedrop_client.gui.base.misc.load_svg", return_value=svg)
    mocker.patch("PyQt5.QtWidgets.QHBoxLayout.addWidget")

    sl = SvgLabel(filename="mock", svg_size=svg_size)

    load_svg_fn.assert_called_once_with("mock")
    sl.svg.setFixedSize.assert_called_once_with(svg_size)
    assert sl.svg == svg


def test_SvgLabel_update(mocker):
    """
    Ensure SvgLabel calls the expected methods correctly to set the icon and size.
    """
    svg = mocker.MagicMock()
    load_svg_fn = mocker.patch("securedrop_client.gui.base.misc.load_svg", return_value=svg)
    mocker.patch("PyQt5.QtWidgets.QHBoxLayout.addWidget")
    sl = SvgLabel(filename="mock", svg_size=QSize(1, 1))

    sl.update_image(filename="mock_two", svg_size=QSize(2, 2))

    assert sl.svg == svg
    assert load_svg_fn.call_args_list[0][0][0] == "mock"
    assert load_svg_fn.call_args_list[1][0][0] == "mock_two"
    assert sl.svg.setFixedSize.call_args_list[0][0][0] == QSize(1, 1)
    assert sl.svg.setFixedSize.call_args_list[1][0][0] == QSize(2, 2)


def test_SecureQLabel_init():
    label_text = '<script>alert("hi!");</script>'
    sl = SecureQLabel(label_text)
    assert sl.text() == label_text


def test_SecureQLabel_init_wordwrap(mocker):
    """
    Regression test to make sure we don't remove newlines.
    """
    long_string = (
        "1234567890123456789012345678901234567890123456789012345678901234567890\n" "12345678901"
    )
    sl = SecureQLabel(long_string, wordwrap=False)
    assert sl.text() == long_string


def test_SecureQLabel_init_no_wordwrap(mocker):
    long_string = (
        "1234567890123456789012345678901234567890123456789012345678901234567890\n" "12345678901"
    )
    sl = SecureQLabel(long_string, wordwrap=False)
    assert sl.text() == long_string


def test_SecureQLabel_setText(mocker):
    sl = SecureQLabel("hello")
    assert sl.text() == "hello"

    label_text = '<script>alert("hi!");</script>'
    sl.setTextFormat = mocker.MagicMock()
    sl.setText(label_text)
    assert sl.text() == label_text
    # Ensure *safe* plain text with no HTML entities.
    sl.setTextFormat.assert_called_once_with(Qt.PlainText)


def test_SecureQLabel_get_elided_text(mocker):
    # 70 character string
    long_string = "1234567890123456789012345678901234567890123456789012345678901234567890"
    sl = SecureQLabel(long_string, wordwrap=False, max_length=100)
    elided_text = sl.get_elided_text(long_string)
    assert sl.text() == elided_text
    assert "…" in elided_text


def test_SecureQLabel_get_elided_text_short_string(mocker):
    # 70 character string
    long_string = "123456789"
    sl = SecureQLabel(long_string, wordwrap=False, max_length=100)
    elided_text = sl.get_elided_text(long_string)
    assert sl.text() == elided_text
    assert elided_text == "123456789"


def test_SecureQLabel_get_elided_text_only_returns_oneline(mocker):
    # 70 character string
    string_with_newline = "this is a string\n with a newline"
    sl = SecureQLabel(string_with_newline, wordwrap=False, max_length=100)
    elided_text = sl.get_elided_text(string_with_newline)
    assert sl.text() == elided_text
    assert elided_text == "this is a string"


def test_SecureQLabel_get_elided_text_only_returns_oneline_elided(mocker):
    # 70 character string
    string_with_newline = "this is a string\n with a newline"
    sl = SecureQLabel(string_with_newline, wordwrap=False, max_length=38)
    elided_text = sl.get_elided_text(string_with_newline)
    assert sl.text() == elided_text
    assert "…" in elided_text


def test_SecureQLabel_quotes_not_escaped_for_readability():
    sl = SecureQLabel("'hello'")
    assert sl.text() == "'hello'"


def test_SecureQLabel_trims_leading_and_trailing_whitespace():
    string_with_whitespace = "\n \n this is a string with leading and trailing whitespace \n"
    sl = SecureQLabel(string_with_whitespace)
    assert sl.text() == "this is a string with leading and trailing whitespace"
