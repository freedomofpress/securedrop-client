from PyQt5.QtGui import QFont, QPalette


def test_styles_for_placeholder(main_window):
    wrapper = main_window.main_view.view_layout.itemAt(0).widget()
    reply_box = wrapper.reply_box
    reply_text_edit = reply_box.text_edit

    sign_in = reply_text_edit.placeholder.signed_out.layout().itemAt(0).widget()
    assert sign_in.font().family() == "Montserrat"
    assert QFont.Bold == sign_in.font().weight()
    assert sign_in.font().pixelSize() == 18
    assert sign_in.palette().color(QPalette.Foreground).name() == "#2a319d"

    to_compose_reply = reply_text_edit.placeholder.signed_out.layout().itemAt(1).widget()
    assert to_compose_reply.font().family() == "Montserrat"
    assert QFont.Normal == to_compose_reply.font().weight()
    assert to_compose_reply.font().pixelSize() == 18
    assert to_compose_reply.palette().color(QPalette.Foreground).name() == "#404040"

    reply_box.set_logged_in()

    compose_a_reply_to = reply_text_edit.placeholder.signed_in.layout().itemAt(0).widget()
    assert compose_a_reply_to.font().family() == "Montserrat"
    assert QFont.Normal == compose_a_reply_to.font().weight()
    assert compose_a_reply_to.font().pixelSize() == 18
    assert compose_a_reply_to.palette().color(QPalette.Foreground).name() == "#404040"

    source_name = reply_text_edit.placeholder.signed_in.layout().itemAt(1).widget()
    assert source_name.font().family() == "Montserrat"
    assert QFont.Bold == source_name.font().weight()
    assert source_name.font().pixelSize() == 18
    assert source_name.palette().color(QPalette.Foreground).name() == "#2a319d"


def test_styles_for_placeholder_no_key(main_window_no_key):
    wrapper = main_window_no_key.main_view.view_layout.itemAt(0).widget()
    reply_box = wrapper.reply_box
    reply_text_edit = reply_box.text_edit

    reply_box.set_logged_in()

    awaiting_key = reply_text_edit.placeholder.signed_in_no_key.layout().itemAt(0).widget()
    assert awaiting_key.font().family() == "Montserrat"
    assert QFont.Bold == awaiting_key.font().weight()
    assert awaiting_key.font().pixelSize() == 18
    assert awaiting_key.palette().color(QPalette.Foreground).name() == "#2a319d"

    from_server = reply_text_edit.placeholder.signed_in_no_key.layout().itemAt(1).widget()
    assert from_server.font().family() == "Montserrat"
    assert QFont.Normal == from_server.font().weight()
    assert from_server.font().pixelSize() == 18
    assert from_server.palette().color(QPalette.Foreground).name() == "#404040"
