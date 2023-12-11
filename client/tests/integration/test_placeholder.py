from PyQt5.QtGui import QFont, QPalette


def test_styles_for_placeholder(main_window):
    wrapper = main_window.main_view.view_layout.itemAt(0).widget()
    reply_box = wrapper.reply_box
    reply_text_edit = reply_box.text_edit

    sign_in = reply_text_edit.placeholder.signed_out.layout().itemAt(0).widget()
    assert "Montserrat" == sign_in.font().family()
    assert QFont.Bold == sign_in.font().weight()
    assert 18 == sign_in.font().pixelSize()
    assert "#2a319d" == sign_in.palette().color(QPalette.Foreground).name()

    to_compose_reply = reply_text_edit.placeholder.signed_out.layout().itemAt(1).widget()
    assert "Montserrat" == to_compose_reply.font().family()
    assert QFont.Normal == to_compose_reply.font().weight()
    assert 18 == to_compose_reply.font().pixelSize()
    assert "#404040" == to_compose_reply.palette().color(QPalette.Foreground).name()

    reply_box.set_logged_in()

    compose_a_reply_to = reply_text_edit.placeholder.signed_in.layout().itemAt(0).widget()
    assert "Montserrat" == compose_a_reply_to.font().family()
    assert QFont.Normal == compose_a_reply_to.font().weight()
    assert 18 == compose_a_reply_to.font().pixelSize()
    assert "#404040" == compose_a_reply_to.palette().color(QPalette.Foreground).name()

    source_name = reply_text_edit.placeholder.signed_in.layout().itemAt(1).widget()
    assert "Montserrat" == source_name.font().family()
    assert QFont.Bold == source_name.font().weight()
    assert 18 == source_name.font().pixelSize()
    assert "#2a319d" == source_name.palette().color(QPalette.Foreground).name()


def test_styles_for_placeholder_no_key(main_window_no_key):
    wrapper = main_window_no_key.main_view.view_layout.itemAt(0).widget()
    reply_box = wrapper.reply_box
    reply_text_edit = reply_box.text_edit

    reply_box.set_logged_in()

    awaiting_key = reply_text_edit.placeholder.signed_in_no_key.layout().itemAt(0).widget()
    assert "Montserrat" == awaiting_key.font().family()
    assert QFont.Bold == awaiting_key.font().weight()
    assert 18 == awaiting_key.font().pixelSize()
    assert "#2a319d" == awaiting_key.palette().color(QPalette.Foreground).name()

    from_server = reply_text_edit.placeholder.signed_in_no_key.layout().itemAt(1).widget()
    assert "Montserrat" == from_server.font().family()
    assert QFont.Normal == from_server.font().weight()
    assert 18 == from_server.font().pixelSize()
    assert "#404040" == from_server.palette().color(QPalette.Foreground).name()
