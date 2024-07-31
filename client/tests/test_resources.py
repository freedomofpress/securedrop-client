"""
Tests for the resources sub-module.
"""

from PyQt5.QtGui import QIcon, QMovie, QPixmap
from PyQt5.QtSvg import QSvgWidget

import securedrop_client.resources


def test_load_icon():
    """
    Check the load_icon function returns the expected QIcon object.
    """
    result = securedrop_client.resources.load_icon(
        "normal_mock",
        "disabled_mock",
        "active_mock",
        "selected_mock",
        "normal_off_mock",
        "disabled_off_mock",
        "active_off_mock",
        "selected_off_mock",
    )
    assert isinstance(result, QIcon)


def test_load_svg():
    """
    Check the load_svg function returns the expected QSvgWidget object.
    """
    result = securedrop_client.resources.load_svg("paperclip.svg")
    assert isinstance(result, QSvgWidget)


def test_load_image():
    """
    Check the load_image function returns the expected QPixmap object.
    """
    result = securedrop_client.resources.load_image("icon")
    assert isinstance(result, QPixmap)


def test_load_movie():
    """
    Check the load_movie function returns the expected QMovie object.
    """
    result = securedrop_client.resources.load_movie("download_animation.gif")
    assert isinstance(result, QMovie)
