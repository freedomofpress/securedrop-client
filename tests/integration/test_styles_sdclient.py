import math

from PyQt5.QtCore import QEvent
from PyQt5.QtGui import QFont, QPalette
from PyQt5.QtWidgets import QLabel, QLineEdit, QPushButton, QWidget


def test_css(main_window):
    login_dialog = main_window.login_dialog
    assert "LoginDialog_form" in login_dialog.styleSheet()


def test_class_name_matches_css_object_name(mocker, main_window):
    # Login Dialog
    login_dialog = main_window.login_dialog
    assert "LoginDialog" == login_dialog.__class__.__name__
    form = login_dialog.layout().itemAt(2).widget()
    assert "LoginDialog" in form.objectName()
    app_version_label = login_dialog.layout().itemAt(4).widget()
    assert "LoginDialog" in app_version_label.objectName()
    login_offline_link = login_dialog.offline_mode
    assert "LoginOfflineLink" == login_offline_link.__class__.__name__
    login_button = login_dialog.submit
    assert "SignInButton" == login_button.__class__.__name__
    assert "SignInButton" in login_button.objectName()
    login_error_bar = login_dialog.error_bar
    assert "LoginErrorBar" == login_error_bar.__class__.__name__
    assert "LoginErrorBar" in login_error_bar.objectName()
    assert "LoginErrorBar" in login_error_bar.error_icon.objectName()
    assert "LoginErrorBar" in login_error_bar.error_status_bar.objectName()

    # Top Pane
    sync_icon = main_window.top_pane.sync_icon
    assert "SyncIcon" == sync_icon.__class__.__name__
    assert "SyncIcon" == sync_icon.objectName()
    activity_status_bar = main_window.top_pane.activity_status_bar
    assert "ActivityStatusBar" == activity_status_bar.__class__.__name__
    assert "ActivityStatusBar" == activity_status_bar.objectName()
    error_status_bar = main_window.top_pane.error_status_bar
    assert "ErrorStatusBar" == error_status_bar.__class__.__name__
    assert "ErrorStatusBar" in error_status_bar.vertical_bar.objectName()
    assert "ErrorStatusBar" in error_status_bar.label.objectName()
    assert "ErrorStatusBar" in error_status_bar.status_bar.objectName()

    # Left Pane
    user_profile = main_window.left_pane.user_profile
    assert "UserProfile" == user_profile.__class__.__name__
    assert "UserProfile" == user_profile.objectName()
    assert "UserProfile" in user_profile.user_icon.objectName()
    user_button = user_profile.user_button
    assert "UserButton" == user_button.__class__.__name__
    assert "UserButton" == user_button.objectName()
    login_button = user_profile.login_button
    assert "LoginButton" == login_button.__class__.__name__
    assert "LoginButton" == login_button.objectName()

    # Main View
    main_view = main_window.main_view
    assert "MainView" == main_view.__class__.__name__
    assert "MainView" == main_view.objectName()
    assert "MainView" in main_view.view_holder.objectName()
    empty_conversation_view = main_view.empty_conversation_view
    "EmptyConversationView" == empty_conversation_view.__class__.__name__
    "EmptyConversationView" == empty_conversation_view.objectName()
    "EmptyConversationView" in empty_conversation_view.no_sources.objectName()
    "EmptyConversationView" in empty_conversation_view.no_source_selected.objectName()
    source_list = main_view.source_list

    source_widget = source_list.itemWidget(source_list.item(0))
    assert "SourceWidget" == source_widget.__class__.__name__
    assert "SourceWidget" in source_widget.name.objectName()
    assert "SourceWidget" in source_widget.preview.objectName()
    assert "SourceWidget" in source_widget.deletion_indicator.objectName()
    assert "SourceWidget" in source_widget.paperclip.objectName()
    assert "SourceWidget" in source_widget.timestamp.objectName()
    assert "SourceWidget" in source_widget.source_widget.objectName()
    star = source_widget.star
    assert "StarToggleButton" == star.__class__.__name__
    assert "StarToggleButton" in star.objectName()

    wrapper = main_view.view_layout.itemAt(0).widget()
    assert "SourceConversationWrapper" == wrapper.__class__.__name__
    assert "SourceDeletionIndicator" == wrapper.deletion_indicator.objectName()
    reply_box = wrapper.reply_box
    assert "ReplyBoxWidget" == reply_box.__class__.__name__
    assert "ReplyBoxWidget" == reply_box.objectName()
    horizontal_line = reply_box.layout().itemAt(0).widget()
    assert "ReplyBoxWidget" in horizontal_line.objectName()
    assert "ReplyBoxWidget" in reply_box.replybox.objectName()
    reply_text_edit = reply_box.text_edit
    assert "ReplyTextEdit" == reply_text_edit.__class__.__name__
    assert "ReplyTextEdit" == reply_text_edit.objectName()
    compose_a_reply_to = reply_text_edit.placeholder.signed_in.layout().itemAt(0).widget()
    source_name = reply_text_edit.placeholder.signed_in.layout().itemAt(1).widget()
    sign_in = reply_text_edit.placeholder.signed_out.layout().itemAt(0).widget()
    to_compose_reply = reply_text_edit.placeholder.signed_in.layout().itemAt(1).widget()
    awaiting_key = reply_text_edit.placeholder.signed_out.layout().itemAt(0).widget()
    from_server = reply_text_edit.placeholder.signed_in.layout().itemAt(1).widget()
    assert "ReplyTextEditPlaceholder" in compose_a_reply_to.objectName()
    assert "ReplyTextEditPlaceholder" in source_name.objectName()
    assert "ReplyTextEditPlaceholder" in sign_in.objectName()
    assert "ReplyTextEditPlaceholder" in to_compose_reply.objectName()
    assert "ReplyTextEditPlaceholder" in awaiting_key.objectName()
    assert "ReplyTextEditPlaceholder" in from_server.objectName()
    conversation_title_bar = wrapper.conversation_title_bar
    assert "SourceProfileShortWidget" == conversation_title_bar.__class__.__name__
    horizontal_line = conversation_title_bar.layout().itemAt(1).widget()
    assert "SourceProfileShortWidget" in horizontal_line.objectName()
    menu = conversation_title_bar.layout().itemAt(0).widget().layout().itemAt(3).widget()
    assert "SourceMenuButton" in menu.objectName()
    last_updated_label = conversation_title_bar.updated
    assert "LastUpdatedLabel" in last_updated_label.objectName()
    title = conversation_title_bar.layout().itemAt(0).widget().layout().itemAt(0).widget()
    assert "TitleLabel" in title.objectName()
    conversation_scroll_area = wrapper.conversation_view.scroll
    assert "ConversationScrollArea" == conversation_scroll_area.__class__.__name__
    assert "ConversationScrollArea" in conversation_scroll_area.widget().objectName()
    file_widget = conversation_scroll_area.widget().layout().itemAt(0).widget()
    assert "FileWidget" == file_widget.__class__.__name__
    message_widget = conversation_scroll_area.widget().layout().itemAt(1).widget()
    assert "MessageWidget" == message_widget.__class__.__name__
    reply_widget = conversation_scroll_area.widget().layout().itemAt(2).widget()
    assert "ReplyWidget" == reply_widget.__class__.__name__
    error_message = reply_widget.error.layout().itemAt(0).widget()
    assert "ReplyWidget" in error_message.objectName()


def test_class_name_matches_css_object_name_for_print_dialog(print_dialog):
    assert "PrintDialog" == print_dialog.__class__.__name__


def test_class_name_matches_css_object_name_for_export_dialog(export_dialog):
    assert "ExportDialog" == export_dialog.__class__.__name__
    assert "ExportDialog" in export_dialog.passphrase_form.objectName()


def test_class_name_matches_css_object_name_for_modal_dialog(modal_dialog):
    assert "ModalDialog" in modal_dialog.header_icon.objectName()
    assert "ModalDialog" in modal_dialog.header_spinner_label.objectName()
    assert "ModalDialog" in modal_dialog.header.objectName()
    assert "ModalDialog" in modal_dialog.header_line.objectName()
    assert "ModalDialog" in modal_dialog.error_details.objectName()
    assert "ModalDialog" in modal_dialog.body.objectName()
    assert "ModalDialog" in modal_dialog.body.objectName()
    assert "ModalDialog" in modal_dialog.continue_button.objectName()
    window_buttons = modal_dialog.layout().itemAt(4).widget()
    assert "ModalDialog" in window_buttons.objectName()
    button_box = window_buttons.layout().itemAt(1).widget()
    assert "ModalDialog" in button_box.objectName()


def test_styles_for_login_dialog(mocker, main_window):
    login_dialog = main_window.login_dialog
    form = login_dialog.layout().itemAt(2).widget()
    form_children_qlabel = form.findChildren(QLabel)
    for c in form_children_qlabel:
        assert "Montserrat" == c.font().family()
        assert QFont.DemiBold - 1 == c.font().weight()
        assert 13 == c.font().pixelSize()
        assert "#ffffff" == c.palette().color(QPalette.Foreground).name()
    form_children_qlineedit = form.findChildren(QLineEdit)
    for c in form_children_qlineedit:
        assert 30 == c.height()  # 30px + 0px margin
        assert (0, 0, 0, 0) == c.getContentsMargins()
    app_version_label = login_dialog.layout().itemAt(4).widget()
    assert "#9fddff" == app_version_label.palette().color(QPalette.Foreground).name()

    login_offline_link = login_dialog.offline_mode
    assert "#ffffff" == login_offline_link.palette().color(QPalette.Foreground).name()

    login_button = login_dialog.submit
    assert "Montserrat" == login_button.font().family()
    assert QFont.Bold == login_button.font().weight()
    assert 14 == login_button.font().pixelSize()
    assert "#2a319d" == login_button.palette().color(QPalette.Foreground).name()
    assert "#05edfe" == login_button.palette().color(QPalette.Background).name()

    login_error_bar = login_dialog.error_bar
    login_error_bar_children = login_error_bar.findChildren(QWidget)
    for c in login_error_bar_children:
        assert "#ce0083" == c.palette().color(QPalette.Background).name()
    assert "#ffffff" == login_error_bar.error_icon.palette().color(QPalette.Foreground).name()
    assert "#ffffff" == login_error_bar.error_status_bar.palette().color(QPalette.Foreground).name()


def test_styles_for_top_pane(mocker, main_window):
    sync_icon = main_window.top_pane.sync_icon
    assert "#ffffff" == sync_icon.palette().color(QPalette.Base).name()
    activity_status_bar = main_window.top_pane.activity_status_bar
    assert "Source Sans Pro" == activity_status_bar.font().family()
    assert QFont.Bold == activity_status_bar.font().weight()
    assert 12 == activity_status_bar.font().pixelSize()
    assert "#ffffff" == activity_status_bar.palette().color(QPalette.Base).name()
    assert "#d3d8ea" == activity_status_bar.palette().color(QPalette.Foreground).name()
    error_status_bar = main_window.top_pane.error_status_bar
    assert "#ff3366" == error_status_bar.vertical_bar.palette().color(QPalette.Background).name()
    assert "Source Sans Pro" == error_status_bar.status_bar.font().family()
    assert QFont.Normal == error_status_bar.status_bar.font().weight()
    assert 14 == error_status_bar.status_bar.font().pixelSize()
    assert "#0c3e75" == error_status_bar.status_bar.palette().color(QPalette.Foreground).name()


def test_styles_for_left_pane(mocker, main_window):
    user_profile = main_window.left_pane.user_profile
    assert "#9211ff" == user_profile.user_icon.palette().color(QPalette.Background).name()
    assert "Source Sans Pro" == user_profile.user_icon.font().family()
    assert QFont.Bold == user_profile.user_icon.font().weight()
    assert 15 == user_profile.user_icon.font().pixelSize()
    assert "#ffffff" == user_profile.user_icon.palette().color(QPalette.Foreground).name()
    user_button = user_profile.user_button
    assert "Source Sans Pro" == user_button.font().family()
    assert QFont.Black == user_button.font().weight()
    assert 12 == user_button.font().pixelSize()
    assert "#ffffff" == user_button.palette().color(QPalette.Foreground).name()
    login_button = user_profile.login_button
    assert "#05edfe" == login_button.palette().color(QPalette.Background).name()
    assert "Montserrat" == login_button.font().family()
    assert QFont.Bold == login_button.font().weight()
    assert 14 == login_button.font().pixelSize()
    assert "#2a319d" == login_button.palette().color(QPalette.Foreground).name()


def test_styles_for_main_view(mocker, main_window):
    main_view = main_window.main_view
    assert 558 == main_view.minimumSize().height()
    assert "#f9f9ff" == main_view.view_holder.palette().color(QPalette.Background).name()

    assert 640 == main_view.empty_conversation_view.minimumSize().width()
    no_sources = main_view.empty_conversation_view.no_sources
    assert 5 == no_sources.layout().count()
    no_sources_instructions = no_sources.layout().itemAt(0).widget()
    assert "Montserrat" == no_sources_instructions.font().family()
    assert QFont.DemiBold - 1 == no_sources_instructions.font().weight()
    assert 35 == no_sources_instructions.font().pixelSize()
    assert "#a5b3e9" == no_sources_instructions.palette().color(QPalette.Foreground).name()
    no_sources_spacer1 = no_sources.layout().itemAt(1)
    assert 35 == no_sources_spacer1.minimumSize().height()
    assert 35 == no_sources_spacer1.maximumSize().height()
    no_sources_instruction_details1 = no_sources.layout().itemAt(2).widget()
    assert "Montserrat" == no_sources_instruction_details1.font().family()
    assert QFont.Normal == no_sources_instruction_details1.font().weight()
    assert 35 == no_sources_instruction_details1.font().pixelSize()
    assert "#a5b3e9" == no_sources_instruction_details1.palette().color(QPalette.Foreground).name()
    no_sources_spacer2 = no_sources.layout().itemAt(3)
    assert 35 == no_sources_spacer2.minimumSize().height()
    assert 35 == no_sources_spacer2.maximumSize().height()
    no_sources_instruction_details2 = no_sources.layout().itemAt(4).widget()
    assert "Montserrat" == no_sources_instruction_details2.font().family()
    assert QFont.Normal == no_sources_instruction_details2.font().weight()
    assert 35 == no_sources_instruction_details2.font().pixelSize()
    assert "#a5b3e9" == no_sources_instruction_details2.palette().color(QPalette.Foreground).name()

    no_source_selected = main_view.empty_conversation_view.no_source_selected
    assert 6 == no_source_selected.layout().count()
    no_source_selected_instructions = no_source_selected.layout().itemAt(0).widget()
    assert "Montserrat" == no_source_selected_instructions.font().family()
    assert QFont.DemiBold - 1 == no_source_selected_instructions.font().weight()
    assert 35 == no_source_selected_instructions.font().pixelSize()
    assert "#a5b3e9" == no_source_selected_instructions.palette().color(QPalette.Foreground).name()
    no_source_selected_spacer1 = no_source_selected.layout().itemAt(1)
    assert 35 == no_source_selected_spacer1.minimumSize().height()
    assert 35 == no_source_selected_spacer1.maximumSize().height()
    bullet1_bullet = no_source_selected.layout().itemAt(2).widget().layout().itemAt(0).widget()
    assert (0, 4, 0, 0) == bullet1_bullet.getContentsMargins()
    35 == bullet1_bullet.font().pixelSize()
    QFont.Bold == bullet1_bullet.font().weight()
    assert "Montserrat" == bullet1_bullet.font().family()
    assert "#a5b3e9" == bullet1_bullet.palette().color(QPalette.Foreground).name()
    bullet2_bullet = no_source_selected.layout().itemAt(3).widget().layout().itemAt(0).widget()
    assert (0, 4, 0, 0) == bullet2_bullet.getContentsMargins()
    35 == bullet2_bullet.font().pixelSize()
    QFont.Bold == bullet2_bullet.font().weight()
    assert "Montserrat" == bullet2_bullet.font().family()
    assert "#a5b3e9" == bullet2_bullet.palette().color(QPalette.Foreground).name()
    bullet3_bullet = no_source_selected.layout().itemAt(4).widget().layout().itemAt(0).widget()
    assert (0, 4, 0, 0) == bullet3_bullet.getContentsMargins()
    35 == bullet3_bullet.font().pixelSize()
    QFont.Bold == bullet3_bullet.font().weight()
    assert "Montserrat" == bullet3_bullet.font().family()
    assert "#a5b3e9" == bullet3_bullet.palette().color(QPalette.Foreground).name()
    no_source_selected_spacer2 = no_source_selected.layout().itemAt(5)
    assert (35 * 4) == no_source_selected_spacer2.minimumSize().height()
    assert (35 * 4) == no_source_selected_spacer2.maximumSize().height()


def test_styles_source_list(mocker, main_window):
    source_list = main_window.main_view.source_list
    source_widget = source_list.itemWidget(source_list.item(0))
    preview = source_widget.preview
    assert "Source Sans Pro" == preview.font().family()
    QFont.Normal == preview.font().weight()
    13 == preview.font().pixelSize()
    assert "#383838" == preview.palette().color(QPalette.Foreground).name()
    deletion_indicator = source_widget.deletion_indicator
    assert "Source Sans Pro" == deletion_indicator.font().family()
    QFont.Normal == deletion_indicator.font().weight()
    13 == deletion_indicator.font().pixelSize()
    assert "#000000" == deletion_indicator.palette().color(QPalette.Foreground).name()
    name = source_widget.name
    assert "Montserrat" == name.font().family()
    QFont.Normal == name.font().weight()
    13 == name.font().pixelSize()
    assert "#2a319d" == name.palette().color(QPalette.Foreground).name()
    timestamp = source_widget.timestamp
    assert "Montserrat" == timestamp.font().family()
    QFont.Normal == timestamp.font().weight()
    13 == timestamp.font().pixelSize()
    assert "#383838" == timestamp.palette().color(QPalette.Foreground).name()


def test_styles_for_conversation_view(mocker, main_window):
    wrapper = main_window.main_view.view_layout.itemAt(0).widget()
    deletion_indicator = wrapper.deletion_indicator
    assert "Montserrat" == deletion_indicator.deletion_message.font().family()
    assert QFont.Normal == deletion_indicator.deletion_message.font().weight()
    assert 30 == deletion_indicator.deletion_message.font().pixelSize()
    assert (
        "#ffffff" == deletion_indicator.deletion_message.palette().color(QPalette.Foreground).name()
    )
    reply_box = wrapper.reply_box
    assert 173 == reply_box.minimumSize().height()
    assert 173 == reply_box.maximumSize().height()
    assert "#ffffff" == reply_box.replybox.palette().color(QPalette.Background).name()
    assert "#ffffff" == reply_box.text_edit.palette().color(QPalette.Background).name()
    reply_box.set_logged_in()
    assert "#ffffff" == reply_box.replybox.palette().color(QPalette.Background).name()
    reply_box_children = reply_box.findChildren(QPushButton)
    hover = QEvent(QEvent.HoverEnter)
    for c in reply_box_children:
        c.eventFilter(c, hover)
    horizontal_line = reply_box.layout().itemAt(0).widget()
    assert 2 == horizontal_line.minimumSize().height()
    assert 2 == horizontal_line.maximumSize().height()
    assert 38 == math.floor(255 * 0.15)  # sanity check
    assert 38 == horizontal_line.palette().color(QPalette.Background).rgba64().alpha8()
    assert 42 == horizontal_line.palette().color(QPalette.Background).red()
    assert 49 == horizontal_line.palette().color(QPalette.Background).green()
    assert 157 == horizontal_line.palette().color(QPalette.Background).blue()
    reply_text_edit = reply_box.text_edit
    assert "Montserrat" == reply_text_edit.font().family()
    assert QFont.Normal == reply_text_edit.font().weight()
    assert 18 == reply_text_edit.font().pixelSize()
    assert (0, 0, 0, 0) == reply_text_edit.getContentsMargins()

    # See test_placeholder.py for placeholder tests

    conversation_title_bar = wrapper.conversation_title_bar
    horizontal_line = conversation_title_bar.layout().itemAt(1).widget()
    assert 2 == horizontal_line.minimumSize().height()
    assert 2 == horizontal_line.maximumSize().height()
    assert 38 == math.floor(255 * 0.15)  # sanity check
    assert 38 == horizontal_line.palette().color(QPalette.Background).rgba64().alpha8()
    assert 42 == horizontal_line.palette().color(QPalette.Background).red()
    assert 49 == horizontal_line.palette().color(QPalette.Background).green()
    assert 157 == horizontal_line.palette().color(QPalette.Background).blue()
    last_updated_label = conversation_title_bar.updated
    assert "Montserrat" == last_updated_label.font().family()
    assert QFont.Light == last_updated_label.font().weight()
    assert 24 == last_updated_label.font().pixelSize()
    assert "#2a319d" == last_updated_label.palette().color(QPalette.Foreground).name()

    title = conversation_title_bar.layout().itemAt(0).widget().layout().itemAt(0).widget()
    assert "Montserrat" == title.font().family()
    assert QFont.Normal == title.font().weight()
    assert 24 == title.font().pixelSize()
    assert "#2a319d" == title.palette().color(QPalette.Foreground).name()

    conversation_scrollarea = wrapper.conversation_view.scroll
    assert "#f9f9ff" == conversation_scrollarea.palette().color(QPalette.Background).name()
    assert "#f9f9ff" == conversation_scrollarea.widget().palette().color(QPalette.Background).name()
    file_widget = conversation_scrollarea.widget().layout().itemAt(0).widget()
    assert 400 == file_widget.minimumSize().width()
    assert 137 == file_widget.file_options.minimumSize().width()
    assert "Source Sans Pro" == file_widget.export_button.font().family()
    assert QFont.DemiBold - 1 == file_widget.export_button.font().weight()
    assert 13 == file_widget.export_button.font().pixelSize()
    assert "#2a319d" == file_widget.export_button.palette().color(QPalette.Foreground).name()
    assert "Source Sans Pro" == file_widget.file_name.font().family()
    assert QFont.Bold == file_widget.file_name.font().weight()
    assert 13 == file_widget.file_name.font().pixelSize()
    assert "#2a319d" == file_widget.file_name.palette().color(QPalette.Foreground).name()
    assert "Source Sans Pro" == file_widget.no_file_name.font().family()
    assert QFont.Light + 12 == file_widget.no_file_name.font().weight()
    assert 13 == file_widget.no_file_name.font().pixelSize()
    assert "#7481b4" == file_widget.no_file_name.palette().color(QPalette.Foreground).name()

    assert 48 == file_widget.file_size.minimumSize().width()
    assert 48 == file_widget.file_size.maximumSize().width()
    assert "Source Sans Pro" == file_widget.file_size.font().family()
    assert QFont.Normal == file_widget.file_size.font().weight()
    assert 13 == file_widget.file_size.font().pixelSize()
    assert "#2a319d" == file_widget.file_size.palette().color(QPalette.Foreground).name()

    assert 2 == file_widget.horizontal_line.minimumSize().height()  # 2px + 0px margin
    assert 2 == file_widget.horizontal_line.maximumSize().height()  # 2px + 0px margin
    assert 114 == math.floor(255 * 0.45)  # sanity check
    assert 114 == file_widget.horizontal_line.palette().color(QPalette.Background).rgba64().alpha8()
    assert 211 == file_widget.horizontal_line.palette().color(QPalette.Background).red()
    assert 216 == file_widget.horizontal_line.palette().color(QPalette.Background).green()
    assert 234 == file_widget.horizontal_line.palette().color(QPalette.Background).blue()

    message_widget = conversation_scrollarea.widget().layout().itemAt(1).widget()
    assert 400 == message_widget.speech_bubble.minimumSize().width()
    reply_widget = conversation_scrollarea.widget().layout().itemAt(2).widget()
    assert 400 == reply_widget.speech_bubble.minimumSize().width()
    reply_widget_error_message = reply_widget.error.layout().itemAt(0).widget()
    assert "Source Sans Pro" == reply_widget_error_message.font().family()
    assert QFont.DemiBold - 1 == reply_widget_error_message.font().weight()
    assert 13 == reply_widget_error_message.font().pixelSize()
    assert "#ff3366" == reply_widget_error_message.palette().color(QPalette.Foreground).name()


def test_styles_for_modal_dialog(modal_dialog):
    assert 800 == modal_dialog.minimumSize().width()
    assert 800 == modal_dialog.maximumSize().width()
    assert 300 == modal_dialog.minimumSize().height()
    assert 800 == modal_dialog.maximumSize().height()
    assert "#ffffff" == modal_dialog.palette().color(QPalette.Background).name()
    assert 110 == modal_dialog.header_icon.minimumSize().width()  # 80px + 30px margin
    assert 110 == modal_dialog.header_icon.maximumSize().width()  # 80px + 30px margin
    assert 64 == modal_dialog.header_icon.minimumSize().height()  # 64px + 0px margin
    assert 64 == modal_dialog.header_icon.maximumSize().height()  # 64px + 0px margin
    assert 110 == modal_dialog.header_spinner_label.minimumSize().width()  # 80px + 30px margin
    assert 110 == modal_dialog.header_spinner_label.maximumSize().width()  # 80px + 30px margin
    assert 64 == modal_dialog.header_spinner_label.minimumSize().height()  # 64px + 0px margin
    assert 64 == modal_dialog.header_spinner_label.maximumSize().height()  # 64px + 0px margin
    assert 68 == modal_dialog.header.minimumSize().height()  # 68px + 0px margin
    assert 68 == modal_dialog.header.maximumSize().height()  # 68px + 0px margin
    assert "Montserrat" == modal_dialog.header.font().family()
    assert QFont.Bold == modal_dialog.header.font().weight()
    assert 24 == modal_dialog.header.font().pixelSize()
    assert "#2a319d" == modal_dialog.header.palette().color(QPalette.Foreground).name()
    assert (0, 0, 0, 0) == modal_dialog.header.getContentsMargins()
    assert 2 == modal_dialog.header_line.minimumSize().height()  # 2px + 20px margin
    assert 2 == modal_dialog.header_line.maximumSize().height()  # 2px + 20px margin
    assert 38 == math.floor(255 * 0.15)  # sanity check
    assert 38 == modal_dialog.header_line.palette().color(QPalette.Background).rgba64().alpha8()
    assert 42 == modal_dialog.header_line.palette().color(QPalette.Background).red()
    assert 49 == modal_dialog.header_line.palette().color(QPalette.Background).green()
    assert 157 == modal_dialog.header_line.palette().color(QPalette.Background).blue()

    assert "Montserrat" == modal_dialog.body.font().family()
    assert 16 == modal_dialog.body.font().pixelSize()
    assert "#302aa3" == modal_dialog.body.palette().color(QPalette.Foreground).name()
    window_buttons = modal_dialog.layout().itemAt(4).widget()
    button_box = window_buttons.layout().itemAt(0).widget()
    button_box_children = button_box.findChildren(QPushButton)
    for c in button_box_children:
        # TODO: Why does the assertion below not work?
        # assert 44 == c.height()  # 40px + 4px of border
        assert "Montserrat" == c.font().family()
        assert QFont.DemiBold - 1 == c.font().weight()
        assert 15 == c.font().pixelSize()
        # TODO: Why do the assertions below not work?
        # assert '#2a319d' == c.palette().color(QPalette.Foreground).name()
        # assert (12, 0, 0, 0) == c.getContentsMargins()
        # assert 'padding-left: 20px;'
        # assert 'padding-right: 20px;'
        # assert 'border: 2px solid #2a319d;'
        # assert 'border: 2px solid rgba(42, 49, 157, 0.4);' for button_box when disabled
        # c.setEnabled(False)
        # assert 102 == math.floor(255 * 0.4)  # sanity check
        # assert 102 == c.palette().color(QPalette.Background).rgba64().alpha8()
        # assert 42 == c.palette().color(QPalette.Background).red()
        # assert 49 == c.palette().color(QPalette.Background).green()
        # assert 157 == c.palette().color(QPalette.Background).blue()


def test_styles_for_print_dialog(print_dialog):
    assert 800 == print_dialog.minimumSize().width()
    assert 800 == print_dialog.maximumSize().width()
    assert 300 == print_dialog.minimumSize().height()
    assert 800 == print_dialog.maximumSize().height()
    assert "#ffffff" == print_dialog.palette().color(QPalette.Background).name()
    assert 110 == print_dialog.header_icon.minimumSize().width()  # 80px + 30px margin
    assert 110 == print_dialog.header_icon.maximumSize().width()  # 80px + 30px margin
    assert 64 == print_dialog.header_icon.minimumSize().height()  # 64px + 0px margin
    assert 64 == print_dialog.header_icon.maximumSize().height()  # 64px + 0px margin
    assert 110 == print_dialog.header_spinner_label.minimumSize().width()  # 80px + 30px margin
    assert 110 == print_dialog.header_spinner_label.maximumSize().width()  # 80px + 30px margin
    assert 64 == print_dialog.header_spinner_label.minimumSize().height()  # 64px + 0px margin
    assert 64 == print_dialog.header_spinner_label.maximumSize().height()  # 64px + 0px margin
    assert 68 == print_dialog.header.minimumSize().height()  # 68px + 0px margin
    assert 68 == print_dialog.header.maximumSize().height()  # 68px + 0px margin
    assert "Montserrat" == print_dialog.header.font().family()
    assert QFont.Bold == print_dialog.header.font().weight()
    assert 24 == print_dialog.header.font().pixelSize()
    assert "#2a319d" == print_dialog.header.palette().color(QPalette.Foreground).name()
    assert (0, 0, 0, 0) == print_dialog.header.getContentsMargins()
    assert 2 == print_dialog.header_line.minimumSize().height()  # 2px + 20px margin
    assert 2 == print_dialog.header_line.maximumSize().height()  # 2px + 20px margin
    assert 38 == math.floor(255 * 0.15)  # sanity check
    assert 38 == print_dialog.header_line.palette().color(QPalette.Background).rgba64().alpha8()
    assert 42 == print_dialog.header_line.palette().color(QPalette.Background).red()
    assert 49 == print_dialog.header_line.palette().color(QPalette.Background).green()
    assert 157 == print_dialog.header_line.palette().color(QPalette.Background).blue()

    assert "Montserrat" == print_dialog.body.font().family()
    assert 16 == print_dialog.body.font().pixelSize()
    assert "#302aa3" == print_dialog.body.palette().color(QPalette.Foreground).name()
    window_buttons = print_dialog.layout().itemAt(4).widget()
    button_box = window_buttons.layout().itemAt(0).widget()
    button_box_children = button_box.findChildren(QPushButton)
    for c in button_box_children:
        assert "Montserrat" == c.font().family()
        assert QFont.DemiBold - 1 == c.font().weight()
        assert 15 == c.font().pixelSize()


def test_styles_for_export_dialog(export_dialog):
    assert 800 == export_dialog.minimumSize().width()
    assert 800 == export_dialog.maximumSize().width()
    assert 300 == export_dialog.minimumSize().height()
    assert 800 == export_dialog.maximumSize().height()
    assert "#ffffff" == export_dialog.palette().color(QPalette.Background).name()
    assert 110 == export_dialog.header_icon.minimumSize().width()  # 80px + 30px margin
    assert 110 == export_dialog.header_icon.maximumSize().width()  # 80px + 30px margin
    assert 64 == export_dialog.header_icon.minimumSize().height()  # 64px + 0px margin
    assert 64 == export_dialog.header_icon.maximumSize().height()  # 64px + 0px margin
    assert 110 == export_dialog.header_spinner_label.minimumSize().width()  # 80px + 30px margin
    assert 110 == export_dialog.header_spinner_label.maximumSize().width()  # 80px + 30px margin
    assert 64 == export_dialog.header_spinner_label.minimumSize().height()  # 64px + 0px margin
    assert 64 == export_dialog.header_spinner_label.maximumSize().height()  # 64px + 0px margin
    assert 68 == export_dialog.header.minimumSize().height()  # 68px + 0px margin
    assert 68 == export_dialog.header.maximumSize().height()  # 68px + 0px margin
    assert "Montserrat" == export_dialog.header.font().family()
    assert QFont.Bold == export_dialog.header.font().weight()
    assert 24 == export_dialog.header.font().pixelSize()
    assert "#2a319d" == export_dialog.header.palette().color(QPalette.Foreground).name()
    assert (0, 0, 0, 0) == export_dialog.header.getContentsMargins()
    assert 2 == export_dialog.header_line.minimumSize().height()  # 2px + 20px margin
    assert 2 == export_dialog.header_line.maximumSize().height()  # 2px + 20px margin
    assert 38 == math.floor(255 * 0.15)  # sanity check
    assert 38 == export_dialog.header_line.palette().color(QPalette.Background).rgba64().alpha8()
    assert 42 == export_dialog.header_line.palette().color(QPalette.Background).red()
    assert 49 == export_dialog.header_line.palette().color(QPalette.Background).green()
    assert 157 == export_dialog.header_line.palette().color(QPalette.Background).blue()

    assert "Montserrat" == export_dialog.body.font().family()
    assert 16 == export_dialog.body.font().pixelSize()
    assert "#302aa3" == export_dialog.body.palette().color(QPalette.Foreground).name()
    window_buttons = export_dialog.layout().itemAt(4).widget()
    button_box = window_buttons.layout().itemAt(0).widget()
    button_box_children = button_box.findChildren(QPushButton)
    for c in button_box_children:
        assert 44 == c.height()  # 40px + 4px of border
        assert "Montserrat" == c.font().family()
        assert QFont.DemiBold - 1 == c.font().weight()
        assert 15 == c.font().pixelSize()

    passphrase_children_qlabel = export_dialog.passphrase_form.findChildren(QLabel)
    for c in passphrase_children_qlabel:
        assert "Montserrat" == c.font().family()
        assert QFont.DemiBold - 1 == c.font().weight()
        assert 12 == c.font().pixelSize()
        assert "#2a319d" == c.palette().color(QPalette.Foreground).name()

    form_children_qlineedit = export_dialog.passphrase_form.findChildren(QLineEdit)
    for c in form_children_qlineedit:
        assert 32 == c.minimumSize().height()  # 30px + 2px padding-bottom
        assert 32 == c.maximumSize().height()  # 30px + 2px padding-bottom
        assert "#f8f8f8" == c.palette().color(QPalette.Background).name()
