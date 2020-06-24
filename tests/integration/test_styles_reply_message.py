from PyQt5.QtGui import QFont, QPalette


def test_styles(mocker, main_window):
    wrapper = main_window.main_view.view_layout.itemAt(0).widget()
    conversation_scrollarea = wrapper.conversation_view.scroll
    reply_widget = conversation_scrollarea.widget().layout().itemAt(2).widget()

    assert 540 == reply_widget.message.minimumSize().width()  # 508px + 32px padding
    assert 540 == reply_widget.message.maximumSize().width()  # 508px + 32px padding
    assert "Source Sans Pro" == reply_widget.message.font().family()
    assert QFont.Normal == reply_widget.message.font().weight()
    assert 15 == reply_widget.message.font().pixelSize()
    assert "#3b3b3b" == reply_widget.message.palette().color(QPalette.Foreground).name()
    assert "#ffffff" == reply_widget.message.palette().color(QPalette.Background).name()

    reply_widget._set_reply_state("PENDING")

    assert 540 == reply_widget.message.minimumSize().width()  # 508px + 32px padding
    assert 540 == reply_widget.message.maximumSize().width()  # 508px + 32px padding
    assert "Source Sans Pro" == reply_widget.message.font().family()
    assert QFont.Normal == reply_widget.message.font().weight()
    assert 15 == reply_widget.message.font().pixelSize()
    assert "#a9aaad" == reply_widget.message.palette().color(QPalette.Foreground).name()
    assert "#f7f8fc" == reply_widget.message.palette().color(QPalette.Background).name()

    reply_widget._set_reply_state("FAILED")

    assert 540 == reply_widget.message.minimumSize().width()  # 508px + 32px padding
    assert 540 == reply_widget.message.maximumSize().width()  # 508px + 32px padding
    assert "Source Sans Pro" == reply_widget.message.font().family()
    assert QFont.Normal == reply_widget.message.font().weight()
    assert 15 == reply_widget.message.font().pixelSize()
    assert "#3b3b3b" == reply_widget.message.palette().color(QPalette.Foreground).name()
    assert "#ffffff" == reply_widget.message.palette().color(QPalette.Background).name()
