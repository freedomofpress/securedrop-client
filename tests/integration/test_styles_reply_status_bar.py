from PyQt5.QtGui import QPalette


def test_styles(mocker, main_window):
    wrapper = main_window.main_view.view_layout.itemAt(0).widget()
    conversation_scrollarea = wrapper.conversation_view.scroll
    reply_widget = conversation_scrollarea.widget().layout().itemAt(2).widget()

    assert 5 == reply_widget.color_bar.minimumSize().height()
    assert 5 == reply_widget.color_bar.maximumSize().height()
    assert "#0065db" == reply_widget.color_bar.palette().color(QPalette.Background).name()
    # assert border: 0px;

    reply_widget.set_pending_styles()

    assert 5 == reply_widget.color_bar.minimumSize().height()
    assert 5 == reply_widget.color_bar.maximumSize().height()
    assert "#0065db" == reply_widget.color_bar.palette().color(QPalette.Background).name()
    # assert border: 0px;

    reply_widget.set_failed_styles()

    assert 5 == reply_widget.color_bar.minimumSize().height()
    assert 5 == reply_widget.color_bar.maximumSize().height()
    assert "#ff3366" == reply_widget.color_bar.palette().color(QPalette.Background).name()
    # assert border: 0px;

    reply_widget.set_error("123", reply_widget.uuid, reply_widget.message.text())

    assert 5 == reply_widget.color_bar.minimumSize().height()
    assert 5 == reply_widget.color_bar.maximumSize().height()
    assert "#bcbfcd" == reply_widget.color_bar.palette().color(QPalette.Background).name()
    # assert border: 0px;
