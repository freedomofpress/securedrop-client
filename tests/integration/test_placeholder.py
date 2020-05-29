def test_styles_for_placeholder(main_window):
    wrapper = main_window.main_view.view_layout.itemAt(0).widget()
    reply_box = wrapper.reply_box
    reply_text_edit = reply_box.text_edit
    reply_placeholder_logged_out = '' \
        '<strong><font color="#2a319d">Sign in </font></strong>to compose or send a reply'
    reply_placeholder_logged_in = '' \
        'Compose a reply to <strong><font color="#24276d">testy-mctestface</font></strong>'

    assert reply_placeholder_logged_out == reply_text_edit.placeholder.text()

    reply_box.set_logged_in()

    assert reply_placeholder_logged_in == reply_text_edit.placeholder.text()
