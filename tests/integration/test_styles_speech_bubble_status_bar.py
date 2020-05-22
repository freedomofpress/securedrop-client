from PyQt5.QtGui import QPalette


def test_styles(mocker, main_window):
    wrapper = main_window.main_view.view_layout.itemAt(0).widget()
    conversation_scrollarea = wrapper.conversation_view.scroll
    speech_bubble = conversation_scrollarea.widget().layout().itemAt(1).widget()

    assert 5 == speech_bubble.color_bar.minimumSize().height()
    assert 5 == speech_bubble.color_bar.maximumSize().height()
    assert '#102781' == speech_bubble.color_bar.palette().color(QPalette.Background).name()
    # assert border: 0px;

    speech_bubble.set_error('123', speech_bubble.uuid, speech_bubble.message.text())

    assert 5 == speech_bubble.color_bar.minimumSize().height()
    assert 5 == speech_bubble.color_bar.maximumSize().height()
    assert '#bcbfcd' == speech_bubble.color_bar.palette().color(QPalette.Background).name()
    # assert border: 0px;
