from PyQt5.QtGui import QFont, QPalette


def test_styles(mocker, main_window):
    wrapper = main_window.main_view.view_layout.itemAt(0).widget()
    conversation_scrollarea = wrapper.conversation_view._scroll
    speech_bubble = conversation_scrollarea.widget().layout().itemAt(1).widget()

    assert speech_bubble.speech_bubble.minimumSize().width() == 400
    assert speech_bubble.message.font().family() == "Source Sans Pro"
    assert QFont.Normal == speech_bubble.message.font().weight()
    assert speech_bubble.message.font().pixelSize() == 15
    assert speech_bubble.message.palette().color(QPalette.Foreground).name() == "#3b3b3b"
    assert speech_bubble.message.palette().color(QPalette.Background).name() == "#ffffff"

    speech_bubble._on_download_error("123", speech_bubble.uuid, speech_bubble.message.text())

    assert speech_bubble.speech_bubble.minimumSize().width() == 400
    assert speech_bubble.message.font().family() == "Source Sans Pro"
    assert QFont.Normal == speech_bubble.message.font().weight()
    assert speech_bubble.message.font().pixelSize() == 15
    assert speech_bubble.message.palette().color(QPalette.Foreground).name() == "#3b3b3b"
    assert speech_bubble.message.font().italic()
    assert round(255 * 0.6) == 153  # sanity check
    assert speech_bubble.message.palette().color(QPalette.Background).rgba64().alpha8() == 153
    assert speech_bubble.message.palette().color(QPalette.Background).red() == 255
    assert speech_bubble.message.palette().color(QPalette.Background).green() == 255
    assert speech_bubble.message.palette().color(QPalette.Background).blue() == 255
