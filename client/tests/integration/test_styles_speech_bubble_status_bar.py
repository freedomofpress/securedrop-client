from PyQt5.QtGui import QPalette


def test_styles(mocker, main_window):
    wrapper = main_window.main_view.view_layout.itemAt(0).widget()
    conversation_scrollarea = wrapper.conversation_view._scroll
    speech_bubble = conversation_scrollarea.widget().layout().itemAt(1).widget()

    assert speech_bubble.color_bar.minimumSize().height() == 5
    assert speech_bubble.color_bar.maximumSize().height() == 5
    assert speech_bubble.color_bar.palette().color(QPalette.Background).name() == "#102781"

    speech_bubble._on_download_error("123", speech_bubble.uuid, speech_bubble.message.text())

    assert speech_bubble.color_bar.minimumSize().height() == 5
    assert speech_bubble.color_bar.maximumSize().height() == 5
    assert speech_bubble.color_bar.palette().color(QPalette.Background).name() == "#bcbfcd"
