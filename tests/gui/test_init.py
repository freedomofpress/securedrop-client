"""
Tests for the gui helper functions in __init__.py
"""

import html

from PyQt5.QtCore import QSize
from PyQt5.QtWidgets import QApplication

from securedrop_client.gui import SecureQLabel, SvgPushButton, SvgLabel, SvgToggleButton

app = QApplication([])


def test_SvgToggleButton_init(mocker):
    """
    Ensure SvgToggleButton is checkable, which allows it to be a toggle button and that the expected
    methods are called correctly to set the icon and size.
    """
    svg_size = QSize(1, 1)
    icon = mocker.MagicMock()
    load_toggle_icon_fn = mocker.patch('securedrop_client.gui.load_toggle_icon', return_value=icon)
    setIcon_fn = mocker.patch('securedrop_client.gui.SvgToggleButton.setIcon')
    setIconSize_fn = mocker.patch('securedrop_client.gui.SvgToggleButton.setIconSize')

    stb = SvgToggleButton(on='mock_on', off='mock_off', svg_size=svg_size)

    assert stb.isCheckable() is True
    load_toggle_icon_fn.assert_called_once_with(on='mock_on', off='mock_off')
    setIcon_fn.assert_called_once_with(icon)
    setIconSize_fn.assert_called_once_with(svg_size)


def test_SvgToggleButton_enable(mocker):
    """
    Ensure enable.
    """
    stb = SvgToggleButton(on='mock_on', off='mock_off')
    stb.enable()
    assert stb.isEnabled() is True


def test_SvgToggleButton_disable(mocker):
    """
    Ensure disable.
    """
    stb = SvgToggleButton(on='mock_on', off='mock_off')
    stb.disable()
    assert stb.isEnabled() is False


def test_SvgToggleButton_toggle(mocker):
    """
    Make sure we're not calling this a toggle button for no reason.
    """
    stb = SvgToggleButton(on='mock_on', off='mock_off')
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
    setIcon_fn = mocker.patch('securedrop_client.gui.SvgToggleButton.setIcon')
    icon = mocker.MagicMock()
    load_toggle_icon_fn = mocker.patch('securedrop_client.gui.load_toggle_icon', return_value=icon)
    stb = SvgToggleButton(on='mock_on', off='mock_off')

    stb.set_icon(on='mock_on', off='mock_off')

    load_toggle_icon_fn.assert_called_with(on='mock_on', off='mock_off')
    setIcon_fn.assert_called_with(icon)
    assert stb.icon == icon


def test_SvgPushButton_init(mocker):
    """
    Ensure SvgPushButton calls the expected methods correctly to set the icon and size.
    """
    svg_size = QSize(1, 1)
    icon = mocker.MagicMock()
    load_icon_fn = mocker.patch('securedrop_client.gui.load_icon', return_value=icon)
    setIcon_fn = mocker.patch('securedrop_client.gui.SvgPushButton.setIcon')
    setIconSize_fn = mocker.patch('securedrop_client.gui.SvgPushButton.setIconSize')

    spb = SvgPushButton(
        normal='mock1', disabled='mock2', active='mock3', selected='mock4', svg_size=svg_size)

    assert spb.isCheckable() is False
    load_icon_fn.assert_called_once_with(
        normal='mock1', disabled='mock2', active='mock3', selected='mock4')
    setIcon_fn.assert_called_once_with(icon)
    setIconSize_fn.assert_called_once_with(svg_size)


def test_SvgPushButton_enable(mocker):
    """
    Ensure enable.
    """
    spb = SvgPushButton(normal='mock1', disabled='mock2', active='mock3', selected='mock4')
    spb.enable()
    assert spb.isEnabled() is True


def test_SvgPushButton_disable(mocker):
    """
    Ensure disable.
    """
    spb = SvgPushButton(normal='mock1', disabled='mock2', active='mock3', selected='mock4')
    spb.disable()
    assert spb.isEnabled() is False


def test_SvgLabel_init(mocker):
    """
    Ensure SvgLabel calls the expected methods correctly to set the icon and size.
    """
    svg_size = QSize(1, 1)
    svg = mocker.MagicMock()
    load_svg_fn = mocker.patch('securedrop_client.gui.load_svg', return_value=svg)
    mocker.patch('securedrop_client.gui.QHBoxLayout.addWidget')

    sl = SvgLabel(filename='mock', svg_size=svg_size)

    load_svg_fn.assert_called_once_with('mock')
    sl.svg.setFixedSize.assert_called_once_with(svg_size)
    assert sl.svg == svg


def test_SecureQLabel_init():
    label_text = '<script>alert("hi!");</script>'
    sl = SecureQLabel(label_text)
    assert sl.text() == html.escape(label_text, quote=False)


def test_SecureQLabel_setText():
    sl = SecureQLabel("hello")
    assert sl.text() == "hello"

    label_text = '<script>alert("hi!");</script>'
    sl.setText(label_text)
    assert sl.text() == html.escape(label_text, quote=False)


def test_SecureQLabel_quotes_not_escaped_for_readability():
    sl = SecureQLabel("'hello'")
    assert sl.text() == "'hello'"
