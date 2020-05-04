from PyQt5.QtGui import QFont, QPalette


def test_styles_for_conversation_view(mocker, main_window):
    wrapper = main_window.main_view.view_layout.itemAt(0).widget()
    conversation_scrollarea = wrapper.conversation_view.scroll
    file_widget = conversation_scrollarea.widget().layout().itemAt(0).widget()
    download_button = file_widget.download_button
    assert 'Source Sans Pro' == download_button.font().family()
    assert QFont.Bold == download_button.font().weight()
    assert 13 == download_button.font().pixelSize()
    assert '#2a319d' == download_button.palette().color(QPalette.Foreground).name()
    # assert 'border: none;' for download_button
    # hover = QEvent(QEvent.HoverEnter)
    # download_button.eventFilter(download_button, hover)
    # assert '#05a6fe' == download_button.palette().color(QPalette.Foreground).name()
    file_widget.start_button_animation()
    assert 'Source Sans Pro' == download_button.font().family()
    assert QFont.Bold == download_button.font().weight()
    assert 13 == download_button.font().pixelSize()
    assert '#05a6fe' == download_button.palette().color(QPalette.Foreground).name()
    # assert 'border: none;' for download_button
    # hover = QEvent(QEvent.HoverEnter)
    # download_button.eventFilter(download_button, hover)
    # assert '#05a6fe' == download_button.palette().color(QPalette.Foreground).name()
