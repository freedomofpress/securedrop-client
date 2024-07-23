from PyQt5.QtCore import QEvent
from PyQt5.QtGui import QFont, QPalette

from securedrop_client.resources import load_icon


def test_styles(mocker, main_window):
    wrapper = main_window.main_view.view_layout.itemAt(0).widget()
    conversation_scrollarea = wrapper.conversation_view._scroll
    file_widget = conversation_scrollarea.widget().layout().itemAt(0).widget()
    download_button = file_widget.download_button

    expected_image = load_icon("download_file.svg").pixmap(20, 20).toImage()
    assert download_button.icon().pixmap(20, 20).toImage() == expected_image
    assert "Source Sans Pro" == download_button.font().family()
    assert QFont.Bold == download_button.font().weight()
    assert 13 == download_button.font().pixelSize()
    assert "#2a319d" == download_button.palette().color(QPalette.Foreground).name()

    file_widget.eventFilter(download_button, QEvent(QEvent.HoverEnter))
    expected_image = load_icon("download_file_hover.svg").pixmap(20, 20).toImage()
    assert download_button.icon().pixmap(20, 20).toImage() == expected_image

    file_widget.eventFilter(download_button, QEvent(QEvent.HoverLeave))
    expected_image = load_icon("download_file.svg").pixmap(20, 20).toImage()
    assert download_button.icon().pixmap(20, 20).toImage() == expected_image
    assert "#2a319d" == download_button.palette().color(QPalette.Foreground).name()


def test_styles_animated(mocker, main_window):
    wrapper = main_window.main_view.view_layout.itemAt(0).widget()
    conversation_scrollarea = wrapper.conversation_view._scroll
    file_widget = conversation_scrollarea.widget().layout().itemAt(0).widget()
    download_button = file_widget.download_button

    file_widget.start_button_animation()

    expected_image = load_icon("download_file.gif").pixmap(20, 20).toImage()
    assert download_button.icon().pixmap(20, 20).toImage() == expected_image
    assert "Source Sans Pro" == download_button.font().family()
    assert QFont.Bold == download_button.font().weight()
    assert 13 == download_button.font().pixelSize()
    assert "#05a6fe" == download_button.palette().color(QPalette.Foreground).name()

    file_widget.eventFilter(download_button, QEvent(QEvent.HoverEnter))
    expected_image = load_icon("download_file.gif").pixmap(20, 20).toImage()
    assert download_button.icon().pixmap(20, 20).toImage() == expected_image
    assert "#05a6fe" == download_button.palette().color(QPalette.Foreground).name()

    file_widget.eventFilter(download_button, QEvent(QEvent.HoverLeave))
    expected_image = load_icon("download_file.gif").pixmap(20, 20).toImage()
    assert download_button.icon().pixmap(20, 20).toImage() == expected_image
    assert "#05a6fe" == download_button.palette().color(QPalette.Foreground).name()
