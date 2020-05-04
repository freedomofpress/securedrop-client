from PyQt5.QtGui import QFont, QPalette


def test_styles(mocker, main_window):
    wrapper = main_window.main_view.view_layout.itemAt(0).widget()
    conversation_scrollarea = wrapper.conversation_view.scroll
    speech_bubble = conversation_scrollarea.widget().layout().itemAt(1).widget()
    assert 540 == speech_bubble.message.minimumSize().width()  # 508px + 32px padding
    assert 540 == speech_bubble.message.maximumSize().width()  # 508px + 32px padding
    assert 'Source Sans Pro' == speech_bubble.message.font().family()
    assert QFont.Normal == speech_bubble.message.font().weight()
    assert 15 == speech_bubble.message.font().pixelSize()
    assert '#3b3b3b' == speech_bubble.message.palette().color(QPalette.Foreground).name()
    assert '#ffffff' == speech_bubble.message.palette().color(QPalette.Background).name()
    speech_bubble.set_error('123', speech_bubble.uuid, speech_bubble.message.text())
    assert 540 == speech_bubble.message.minimumSize().width()  # 508px + 32px padding
    assert 540 == speech_bubble.message.maximumSize().width()  # 508px + 32px padding
    assert 'Source Sans Pro' == speech_bubble.message.font().family()
    assert QFont.Normal == speech_bubble.message.font().weight()
    assert 15 == speech_bubble.message.font().pixelSize()
    assert '#3b3b3b' == speech_bubble.message.palette().color(QPalette.Foreground).name()
    # font-style: italic;
    # background-color: rgba(255, 255, 255, 0.6);
