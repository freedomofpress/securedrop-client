from PyQt5.QtGui import QPalette


def test_styles(mocker, main_window):
    wrapper = main_window.main_view.view_layout.itemAt(0).widget()
    conversation_scrollarea = wrapper.conversation_view._scroll
    reply_widget = conversation_scrollarea.widget().layout().itemAt(2).widget()
    reply_widget.sender_is_current_user = False

    assert reply_widget.color_bar.minimumSize().height() == 5
    assert reply_widget.color_bar.maximumSize().height() == 5
    assert reply_widget.color_bar.palette().color(QPalette.Background).name() == "#9211ff"

    reply_widget.set_pending_styles()

    assert reply_widget.color_bar.minimumSize().height() == 5
    assert reply_widget.color_bar.maximumSize().height() == 5
    assert reply_widget.color_bar.palette().color(QPalette.Background).name() == "#0065db"

    reply_widget.set_failed_styles()

    assert reply_widget.color_bar.minimumSize().height() == 5
    assert reply_widget.color_bar.maximumSize().height() == 5
    assert reply_widget.color_bar.palette().color(QPalette.Background).name() == "#ff3366"


def test_styles_for_replies_from_authenticated_user(mocker, main_window):
    wrapper = main_window.main_view.view_layout.itemAt(0).widget()
    conversation_scrollarea = wrapper.conversation_view._scroll
    reply_widget = conversation_scrollarea.widget().layout().itemAt(2).widget()
    reply_widget.sender_is_current_user = True

    assert reply_widget.color_bar.minimumSize().height() == 5
    assert reply_widget.color_bar.maximumSize().height() == 5
    assert reply_widget.color_bar.palette().color(QPalette.Background).name() == "#9211ff"

    reply_widget.set_pending_styles()

    assert reply_widget.color_bar.minimumSize().height() == 5
    assert reply_widget.color_bar.maximumSize().height() == 5
    assert reply_widget.color_bar.palette().color(QPalette.Background).name() == "#9211ff"

    reply_widget.set_failed_styles()

    assert reply_widget.color_bar.minimumSize().height() == 5
    assert reply_widget.color_bar.maximumSize().height() == 5
    assert reply_widget.color_bar.palette().color(QPalette.Background).name() == "#ff3366"

    reply_widget._on_download_error("123", reply_widget.uuid, reply_widget.message.text())

    assert reply_widget.color_bar.minimumSize().height() == 5
    assert reply_widget.color_bar.maximumSize().height() == 5
    assert reply_widget.color_bar.palette().color(QPalette.Background).name() == "#bcbfcd"
