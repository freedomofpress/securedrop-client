from PyQt5.QtGui import QFont, QPalette


def test_styles(mocker, main_window):
    wrapper = main_window.main_view.view_layout.itemAt(0).widget()
    conversation_scrollarea = wrapper.conversation_view._scroll
    speech_bubble = conversation_scrollarea.widget().layout().itemAt(1).widget()

    assert 400 == speech_bubble.speech_bubble.minimumSize().width()
    assert "Source Sans Pro" == speech_bubble.message.font().family()
    assert QFont.Normal == speech_bubble.message.font().weight()
    assert 15 == speech_bubble.message.font().pixelSize()
    assert "#3b3b3b" == speech_bubble.message.palette().color(QPalette.Foreground).name()
    assert "#ffffff" == speech_bubble.message.palette().color(QPalette.Background).name()

    speech_bubble._on_download_error("123", speech_bubble.uuid, speech_bubble.message.text())

    assert 400 == speech_bubble.speech_bubble.minimumSize().width()
    assert "Source Sans Pro" == speech_bubble.message.font().family()
    assert QFont.Normal == speech_bubble.message.font().weight()
    assert 15 == speech_bubble.message.font().pixelSize()
    assert "#3b3b3b" == speech_bubble.message.palette().color(QPalette.Foreground).name()
    assert speech_bubble.message.font().italic()
    assert 153 == round(255 * 0.6)  # sanity check
    assert 153 == speech_bubble.message.palette().color(QPalette.Background).rgba64().alpha8()
    assert 255 == speech_bubble.message.palette().color(QPalette.Background).red()
    assert 255 == speech_bubble.message.palette().color(QPalette.Background).green()
    assert 255 == speech_bubble.message.palette().color(QPalette.Background).blue()
