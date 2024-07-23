import math

from PyQt5.QtCore import QEvent
from PyQt5.QtGui import QFont, QPalette
from PyQt5.QtWidgets import QLabel, QLineEdit, QPushButton, QWidget

from securedrop_client.gui.conversation.export.export_wizard_page import (
    PassphraseWizardPage,
    PreflightPage,
)


def test_css(main_window):
    login_dialog = main_window.login_dialog
    assert "LoginDialog_form" in login_dialog.styleSheet()


def test_class_name_matches_css_object_name(mocker, main_window):
    # Login Dialog
    login_dialog = main_window.login_dialog
    assert login_dialog.__class__.__name__ == "LoginDialog"
    form = login_dialog.layout().itemAt(2).widget()
    assert "LoginDialog" in form.objectName()
    app_version_label = login_dialog.layout().itemAt(4).widget()
    assert "LoginDialog" in app_version_label.objectName()
    login_offline_link = login_dialog.offline_mode
    assert login_offline_link.__class__.__name__ == "LoginOfflineLink"
    login_button = login_dialog.submit
    assert login_button.__class__.__name__ == "SignInButton"
    assert "SignInButton" in login_button.objectName()
    login_error_bar = login_dialog.error_bar
    assert login_error_bar.__class__.__name__ == "LoginErrorBar"
    assert "LoginErrorBar" in login_error_bar.objectName()
    assert "LoginErrorBar" in login_error_bar.error_icon.objectName()
    assert "LoginErrorBar" in login_error_bar.error_status_bar.objectName()

    # Top Pane
    sync_icon = main_window.top_pane.sync_icon
    assert sync_icon.__class__.__name__ == "SyncIcon"
    assert sync_icon.objectName() == "SyncIcon"
    activity_status_bar = main_window.top_pane.activity_status_bar
    assert activity_status_bar.__class__.__name__ == "ActivityStatusBar"
    assert activity_status_bar.objectName() == "ActivityStatusBar"
    error_status_bar = main_window.top_pane.error_status_bar
    assert error_status_bar.__class__.__name__ == "ErrorStatusBar"
    assert "ErrorStatusBar" in error_status_bar.vertical_bar.objectName()
    assert "ErrorStatusBar" in error_status_bar.label.objectName()
    assert "ErrorStatusBar" in error_status_bar.status_bar.objectName()

    # Left Pane
    user_profile = main_window.left_pane.user_profile
    assert user_profile.__class__.__name__ == "UserProfile"
    assert user_profile.objectName() == "UserProfile"
    assert "UserProfile" in user_profile.user_icon.objectName()
    user_button = user_profile.user_button
    assert user_button.__class__.__name__ == "UserButton"
    assert user_button.objectName() == "UserButton"
    login_button = user_profile.login_button
    assert login_button.__class__.__name__ == "LoginButton"
    assert login_button.objectName() == "LoginButton"

    # Main View
    main_view = main_window.main_view
    assert main_view.__class__.__name__ == "MainView"
    assert main_view.objectName() == "MainView"
    assert "MainView" in main_view.view_holder.objectName()
    empty_conversation_view = main_view.empty_conversation_view
    empty_conversation_view.__class__.__name__ == "EmptyConversationView"
    empty_conversation_view.objectName() == "EmptyConversationView"
    "EmptyConversationView" in empty_conversation_view.no_sources.objectName()
    "EmptyConversationView" in empty_conversation_view.no_source_selected.objectName()
    source_list = main_view.source_list

    source_widget = source_list.itemWidget(source_list.item(0))
    assert source_widget.__class__.__name__ == "SourceWidget"
    assert "SourceWidget" in source_widget.name.objectName()
    assert "SourceWidget" in source_widget.preview.objectName()
    assert "SourceWidget" in source_widget.deletion_indicator.objectName()
    assert "SourceWidget" in source_widget.paperclip.objectName()
    assert "SourceWidget" in source_widget.timestamp.objectName()
    assert "SourceWidget" in source_widget.source_widget.objectName()
    star = source_widget.star
    assert star.__class__.__name__ == "StarToggleButton"
    assert "StarToggleButton" in star.objectName()

    wrapper = main_view.view_layout.itemAt(0).widget()
    assert wrapper.__class__.__name__ == "SourceConversationWrapper"
    assert wrapper.deletion_indicator.objectName() == "SourceDeletionIndicator"
    reply_box = wrapper.reply_box
    assert reply_box.__class__.__name__ == "ReplyBoxWidget"
    assert reply_box.objectName() == "ReplyBoxWidget"
    horizontal_line = reply_box.layout().itemAt(0).widget()
    assert "ReplyBoxWidget" in horizontal_line.objectName()
    assert "ReplyBoxWidget" in reply_box.replybox.objectName()
    reply_text_edit = reply_box.text_edit
    assert reply_text_edit.__class__.__name__ == "ReplyTextEdit"
    assert reply_text_edit.objectName() == "ReplyTextEdit"
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
    assert conversation_title_bar.__class__.__name__ == "SourceProfileShortWidget"
    horizontal_line = conversation_title_bar.layout().itemAt(1).widget()
    assert "SourceProfileShortWidget" in horizontal_line.objectName()
    menu = conversation_title_bar.layout().itemAt(0).widget().layout().itemAt(3).widget()
    assert "SourceMenuButton" in menu.objectName()
    last_updated_label = conversation_title_bar.updated
    assert "LastUpdatedLabel" in last_updated_label.objectName()
    title = conversation_title_bar.layout().itemAt(0).widget().layout().itemAt(0).widget()
    assert "TitleLabel" in title.objectName()
    conversation_scroll_area = wrapper.conversation_view._scroll
    assert conversation_scroll_area.__class__.__name__ == "ConversationScrollArea"
    assert "ConversationScrollArea" in conversation_scroll_area.widget().objectName()
    file_widget = conversation_scroll_area.widget().layout().itemAt(0).widget()
    assert file_widget.__class__.__name__ == "FileWidget"
    message_widget = conversation_scroll_area.widget().layout().itemAt(1).widget()
    assert message_widget.__class__.__name__ == "MessageWidget"
    reply_widget = conversation_scroll_area.widget().layout().itemAt(2).widget()
    assert reply_widget.__class__.__name__ == "ReplyWidget"
    error_message = reply_widget.error.layout().itemAt(0).widget()
    assert "ReplyWidget" in error_message.objectName()


def test_class_name_matches_css_object_name_for_print_dialog(print_dialog):
    assert print_dialog.__class__.__name__ == "PrintDialog"


def test_class_name_matches_css_object_name_for_export_file_dialog(export_file_wizard):
    assert export_file_wizard.__class__.__name__ == "ExportWizard"
    assert "QWizard_export" in export_file_wizard.objectName()


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
        assert c.font().family() == "Montserrat" or c.font().family() == "Source Sans Pro"
        assert QFont.DemiBold - 1 == c.font().weight()
        assert c.font().pixelSize() == 13 or c.font().pixelSize() == 12
        assert c.palette().color(QPalette.Foreground).name() == "#ffffff"
    form_children_qlineedit = form.findChildren(QLineEdit)
    for c in form_children_qlineedit:
        assert c.height() == 30  # 30px + 0px margin
        assert c.getContentsMargins() == (0, 0, 0, 0)
    app_version_label = login_dialog.layout().itemAt(4).widget()
    assert app_version_label.palette().color(QPalette.Foreground).name() == "#9fddff"

    login_offline_link = login_dialog.offline_mode
    assert login_offline_link.palette().color(QPalette.Foreground).name() == "#ffffff"

    login_button = login_dialog.submit
    assert login_button.font().family() == "Montserrat"
    assert QFont.Bold == login_button.font().weight()
    assert login_button.font().pixelSize() == 14
    assert login_button.palette().color(QPalette.Foreground).name() == "#2a319d"
    assert login_button.palette().color(QPalette.Background).name() == "#05edfe"

    login_error_bar = login_dialog.error_bar
    login_error_bar_children = login_error_bar.findChildren(QWidget)
    for c in login_error_bar_children:
        assert c.palette().color(QPalette.Background).name() == "#ce0083"
    assert login_error_bar.error_icon.palette().color(QPalette.Foreground).name() == "#ffffff"
    assert login_error_bar.error_status_bar.palette().color(QPalette.Foreground).name() == "#ffffff"


def test_styles_for_top_pane(mocker, main_window):
    sync_icon = main_window.top_pane.sync_icon
    assert sync_icon.palette().color(QPalette.Base).name() == "#ffffff"
    activity_status_bar = main_window.top_pane.activity_status_bar
    assert activity_status_bar.font().family() == "Source Sans Pro"
    assert QFont.Bold == activity_status_bar.font().weight()
    assert activity_status_bar.font().pixelSize() == 12
    assert activity_status_bar.palette().color(QPalette.Base).name() == "#000000"
    assert activity_status_bar.palette().color(QPalette.Foreground).name() == "#d3d8ea"
    error_status_bar = main_window.top_pane.error_status_bar
    assert error_status_bar.vertical_bar.palette().color(QPalette.Background).name() == "#ff3366"
    assert error_status_bar.status_bar.font().family() == "Source Sans Pro"
    assert QFont.Normal == error_status_bar.status_bar.font().weight()
    assert error_status_bar.status_bar.font().pixelSize() == 14
    assert error_status_bar.status_bar.palette().color(QPalette.Foreground).name() == "#0c3e75"


def test_styles_for_left_pane(mocker, main_window):
    user_profile = main_window.left_pane.user_profile
    assert user_profile.user_icon.palette().color(QPalette.Background).name() == "#9211ff"
    assert user_profile.user_icon.font().family() == "Source Sans Pro"
    assert QFont.Bold == user_profile.user_icon.font().weight()
    assert user_profile.user_icon.font().pixelSize() == 15
    assert user_profile.user_icon.palette().color(QPalette.Foreground).name() == "#ffffff"
    user_button = user_profile.user_button
    assert user_button.font().family() == "Source Sans Pro"
    assert QFont.Black == user_button.font().weight()
    assert user_button.font().pixelSize() == 12
    assert user_button.palette().color(QPalette.Foreground).name() == "#ffffff"
    login_button = user_profile.login_button
    assert login_button.palette().color(QPalette.Background).name() == "#05edfe"
    assert login_button.font().family() == "Montserrat"
    assert QFont.Bold == login_button.font().weight()
    assert login_button.font().pixelSize() == 14
    assert login_button.palette().color(QPalette.Foreground).name() == "#2a319d"


def test_styles_for_main_view(mocker, main_window):
    main_view = main_window.main_view
    assert main_view.minimumSize().height() == 558
    assert main_view.view_holder.palette().color(QPalette.Background).name() == "#f9f9ff"

    assert main_view.empty_conversation_view.minimumSize().width() == 640
    no_sources = main_view.empty_conversation_view.no_sources
    assert no_sources.layout().count() == 5
    no_sources_instructions = no_sources.layout().itemAt(0).widget()
    assert no_sources_instructions.font().family() == "Montserrat"
    assert QFont.DemiBold - 1 == no_sources_instructions.font().weight()
    assert no_sources_instructions.font().pixelSize() == 35
    assert no_sources_instructions.palette().color(QPalette.Foreground).name() == "#a5b3e9"
    no_sources_spacer1 = no_sources.layout().itemAt(1)
    assert no_sources_spacer1.minimumSize().height() == 35
    assert no_sources_spacer1.maximumSize().height() == 35
    no_sources_instruction_details1 = no_sources.layout().itemAt(2).widget()
    assert no_sources_instruction_details1.font().family() == "Montserrat"
    assert QFont.Normal == no_sources_instruction_details1.font().weight()
    assert no_sources_instruction_details1.font().pixelSize() == 35
    assert no_sources_instruction_details1.palette().color(QPalette.Foreground).name() == "#a5b3e9"
    no_sources_spacer2 = no_sources.layout().itemAt(3)
    assert no_sources_spacer2.minimumSize().height() == 35
    assert no_sources_spacer2.maximumSize().height() == 35
    no_sources_instruction_details2 = no_sources.layout().itemAt(4).widget()
    assert no_sources_instruction_details2.font().family() == "Montserrat"
    assert QFont.Normal == no_sources_instruction_details2.font().weight()
    assert no_sources_instruction_details2.font().pixelSize() == 35
    assert no_sources_instruction_details2.palette().color(QPalette.Foreground).name() == "#a5b3e9"

    no_source_selected = main_view.empty_conversation_view.no_source_selected
    assert no_source_selected.layout().count() == 6
    no_source_selected_instructions = no_source_selected.layout().itemAt(0).widget()
    assert no_source_selected_instructions.font().family() == "Montserrat"
    assert QFont.DemiBold - 1 == no_source_selected_instructions.font().weight()
    assert no_source_selected_instructions.font().pixelSize() == 35
    assert no_source_selected_instructions.palette().color(QPalette.Foreground).name() == "#a5b3e9"
    no_source_selected_spacer1 = no_source_selected.layout().itemAt(1)
    assert no_source_selected_spacer1.minimumSize().height() == 35
    assert no_source_selected_spacer1.maximumSize().height() == 35
    bullet1_bullet = no_source_selected.layout().itemAt(2).widget().layout().itemAt(0).widget()
    assert bullet1_bullet.getContentsMargins() == (0, 4, 0, 0)
    bullet1_bullet.font().pixelSize() == 35
    QFont.Bold == bullet1_bullet.font().weight()
    assert bullet1_bullet.font().family() == "Montserrat"
    assert bullet1_bullet.palette().color(QPalette.Foreground).name() == "#a5b3e9"
    bullet2_bullet = no_source_selected.layout().itemAt(3).widget().layout().itemAt(0).widget()
    assert bullet2_bullet.getContentsMargins() == (0, 4, 0, 0)
    bullet2_bullet.font().pixelSize() == 35
    QFont.Bold == bullet2_bullet.font().weight()
    assert bullet2_bullet.font().family() == "Montserrat"
    assert bullet2_bullet.palette().color(QPalette.Foreground).name() == "#a5b3e9"
    bullet3_bullet = no_source_selected.layout().itemAt(4).widget().layout().itemAt(0).widget()
    assert bullet3_bullet.getContentsMargins() == (0, 4, 0, 0)
    bullet3_bullet.font().pixelSize() == 35
    QFont.Bold == bullet3_bullet.font().weight()
    assert bullet3_bullet.font().family() == "Montserrat"
    assert bullet3_bullet.palette().color(QPalette.Foreground).name() == "#a5b3e9"
    no_source_selected_spacer2 = no_source_selected.layout().itemAt(5)
    assert no_source_selected_spacer2.minimumSize().height() == (35 * 4)
    assert no_source_selected_spacer2.maximumSize().height() == (35 * 4)


def test_styles_source_list(mocker, main_window):
    source_list = main_window.main_view.source_list
    source_widget = source_list.itemWidget(source_list.item(0))
    preview = source_widget.preview
    assert preview.font().family() == "Source Sans Pro"
    QFont.Normal == preview.font().weight()
    preview.font().pixelSize() == 13
    assert preview.palette().color(QPalette.Foreground).name() == "#383838"
    deletion_indicator = source_widget.deletion_indicator
    assert deletion_indicator.font().family() == "Source Sans Pro"
    QFont.Normal == deletion_indicator.font().weight()
    deletion_indicator.font().pixelSize() == 13
    assert deletion_indicator.palette().color(QPalette.Foreground).name() == "#000000"
    name = source_widget.name
    assert name.font().family() == "Montserrat"
    QFont.Normal == name.font().weight()
    name.font().pixelSize() == 13
    assert name.palette().color(QPalette.Foreground).name() == "#2a319d"
    timestamp = source_widget.timestamp
    assert timestamp.font().family() == "Montserrat"
    QFont.Normal == timestamp.font().weight()
    timestamp.font().pixelSize() == 13
    assert timestamp.palette().color(QPalette.Foreground).name() == "#383838"


def test_styles_for_conversation_view(mocker, main_window):
    wrapper = main_window.main_view.view_layout.itemAt(0).widget()
    deletion_indicator = wrapper.deletion_indicator
    assert deletion_indicator.deletion_message.font().family() == "Montserrat"
    assert QFont.Normal == deletion_indicator.deletion_message.font().weight()
    assert deletion_indicator.deletion_message.font().pixelSize() == 30
    assert (
        deletion_indicator.deletion_message.palette().color(QPalette.Foreground).name() == "#ffffff"
    )
    reply_box = wrapper.reply_box
    assert reply_box.minimumSize().height() == 173
    assert reply_box.maximumSize().height() == 173
    assert reply_box.replybox.palette().color(QPalette.Background).name() == "#ffffff"
    assert reply_box.text_edit.palette().color(QPalette.Background).name() == "#ffffff"
    reply_box.set_logged_in()
    assert reply_box.replybox.palette().color(QPalette.Background).name() == "#ffffff"
    reply_box_children = reply_box.findChildren(QPushButton)
    hover = QEvent(QEvent.HoverEnter)
    for c in reply_box_children:
        c.eventFilter(c, hover)
    horizontal_line = reply_box.layout().itemAt(0).widget()
    assert horizontal_line.minimumSize().height() == 2
    assert horizontal_line.maximumSize().height() == 2
    assert math.floor(255 * 0.15) == 38  # sanity check
    assert horizontal_line.palette().color(QPalette.Background).rgba64().alpha8() == 38
    assert horizontal_line.palette().color(QPalette.Background).red() == 42
    assert horizontal_line.palette().color(QPalette.Background).green() == 49
    assert horizontal_line.palette().color(QPalette.Background).blue() == 157
    reply_text_edit = reply_box.text_edit
    assert reply_text_edit.font().family() == "Montserrat"
    assert QFont.Normal == reply_text_edit.font().weight()
    assert reply_text_edit.font().pixelSize() == 18
    assert reply_text_edit.getContentsMargins() == (0, 0, 0, 0)

    # See test_placeholder.py for placeholder tests

    conversation_title_bar = wrapper.conversation_title_bar
    horizontal_line = conversation_title_bar.layout().itemAt(1).widget()
    assert horizontal_line.minimumSize().height() == 2
    assert horizontal_line.maximumSize().height() == 2
    assert math.floor(255 * 0.15) == 38  # sanity check
    assert horizontal_line.palette().color(QPalette.Background).rgba64().alpha8() == 38
    assert horizontal_line.palette().color(QPalette.Background).red() == 42
    assert horizontal_line.palette().color(QPalette.Background).green() == 49
    assert horizontal_line.palette().color(QPalette.Background).blue() == 157
    last_updated_label = conversation_title_bar.updated
    assert last_updated_label.font().family() == "Montserrat"
    assert QFont.Light == last_updated_label.font().weight()
    assert last_updated_label.font().pixelSize() == 24
    assert last_updated_label.palette().color(QPalette.Foreground).name() == "#2a319d"

    title = conversation_title_bar.layout().itemAt(0).widget().layout().itemAt(0).widget()
    assert title.font().family() == "Montserrat"
    assert QFont.Normal == title.font().weight()
    assert title.font().pixelSize() == 24
    assert title.palette().color(QPalette.Foreground).name() == "#2a319d"

    conversation_scrollarea = wrapper.conversation_view._scroll
    assert conversation_scrollarea.palette().color(QPalette.Background).name() == "#f9f9ff"
    assert conversation_scrollarea.widget().palette().color(QPalette.Background).name() == "#f9f9ff"
    file_widget = conversation_scrollarea.widget().layout().itemAt(0).widget()
    assert file_widget.minimumSize().width() == 400
    assert file_widget.file_options.minimumSize().width() == 137
    assert file_widget.export_button.font().family() == "Source Sans Pro"
    assert QFont.DemiBold - 1 == file_widget.export_button.font().weight()
    assert file_widget.export_button.font().pixelSize() == 13
    assert file_widget.export_button.palette().color(QPalette.Foreground).name() == "#2a319d"
    assert file_widget.file_name.font().family() == "Source Sans Pro"
    assert QFont.Bold == file_widget.file_name.font().weight()
    assert file_widget.file_name.font().pixelSize() == 13
    assert file_widget.file_name.palette().color(QPalette.Foreground).name() == "#2a319d"
    assert file_widget.no_file_name.font().family() == "Source Sans Pro"
    assert QFont.Light + 12 == file_widget.no_file_name.font().weight()
    assert file_widget.no_file_name.font().pixelSize() == 13
    assert file_widget.no_file_name.palette().color(QPalette.Foreground).name() == "#7481b4"

    assert file_widget.file_size.minimumSize().width() == 48
    assert file_widget.file_size.maximumSize().width() == 48
    assert file_widget.file_size.font().family() == "Source Sans Pro"
    assert QFont.Normal == file_widget.file_size.font().weight()
    assert file_widget.file_size.font().pixelSize() == 13
    assert file_widget.file_size.palette().color(QPalette.Foreground).name() == "#2a319d"

    assert file_widget.horizontal_line.minimumSize().height() == 2  # 2px + 0px margin
    assert file_widget.horizontal_line.maximumSize().height() == 2  # 2px + 0px margin
    assert math.floor(255 * 0.45) == 114  # sanity check
    assert file_widget.horizontal_line.palette().color(QPalette.Background).rgba64().alpha8() == 114
    assert file_widget.horizontal_line.palette().color(QPalette.Background).red() == 211
    assert file_widget.horizontal_line.palette().color(QPalette.Background).green() == 216
    assert file_widget.horizontal_line.palette().color(QPalette.Background).blue() == 234

    message_widget = conversation_scrollarea.widget().layout().itemAt(1).widget()
    assert message_widget.speech_bubble.minimumSize().width() == 400
    reply_widget = conversation_scrollarea.widget().layout().itemAt(2).widget()
    assert reply_widget.speech_bubble.minimumSize().width() == 400
    reply_widget_error_message = reply_widget.error.layout().itemAt(0).widget()
    assert reply_widget_error_message.font().family() == "Source Sans Pro"
    assert QFont.DemiBold - 1 == reply_widget_error_message.font().weight()
    assert reply_widget_error_message.font().pixelSize() == 13
    assert reply_widget_error_message.palette().color(QPalette.Foreground).name() == "#ff3366"


def test_styles_for_modal_dialog(modal_dialog):
    assert modal_dialog.minimumSize().width() == 800
    assert modal_dialog.maximumSize().width() == 800
    assert modal_dialog.minimumSize().height() == 300
    assert modal_dialog.maximumSize().height() == 800
    assert modal_dialog.palette().color(QPalette.Background).name() == "#ffffff"
    assert modal_dialog.header_icon.minimumSize().width() == 110  # 80px + 30px margin
    assert modal_dialog.header_icon.maximumSize().width() == 110  # 80px + 30px margin
    assert modal_dialog.header_icon.minimumSize().height() == 64  # 64px + 0px margin
    assert modal_dialog.header_icon.maximumSize().height() == 64  # 64px + 0px margin
    assert modal_dialog.header_spinner_label.minimumSize().width() == 110  # 80px + 30px margin
    assert modal_dialog.header_spinner_label.maximumSize().width() == 110  # 80px + 30px margin
    assert modal_dialog.header_spinner_label.minimumSize().height() == 64  # 64px + 0px margin
    assert modal_dialog.header_spinner_label.maximumSize().height() == 64  # 64px + 0px margin
    assert modal_dialog.header.minimumSize().height() == 68  # 68px + 0px margin
    assert modal_dialog.header.maximumSize().height() == 68  # 68px + 0px margin
    assert modal_dialog.header.font().family() == "Montserrat"
    assert QFont.Bold == modal_dialog.header.font().weight()
    assert modal_dialog.header.font().pixelSize() == 24
    assert modal_dialog.header.palette().color(QPalette.Foreground).name() == "#2a319d"
    assert modal_dialog.header.getContentsMargins() == (0, 0, 0, 0)
    assert modal_dialog.header_line.minimumSize().height() == 2  # 2px + 20px margin
    assert modal_dialog.header_line.maximumSize().height() == 2  # 2px + 20px margin
    assert math.floor(255 * 0.15) == 38  # sanity check
    assert modal_dialog.header_line.palette().color(QPalette.Background).rgba64().alpha8() == 38
    assert modal_dialog.header_line.palette().color(QPalette.Background).red() == 42
    assert modal_dialog.header_line.palette().color(QPalette.Background).green() == 49
    assert modal_dialog.header_line.palette().color(QPalette.Background).blue() == 157

    assert modal_dialog.body.font().family() == "Montserrat"
    assert modal_dialog.body.font().pixelSize() == 16
    assert modal_dialog.body.palette().color(QPalette.Foreground).name() == "#302aa3"
    window_buttons = modal_dialog.layout().itemAt(4).widget()
    button_box = window_buttons.layout().itemAt(0).widget()
    button_box_children = button_box.findChildren(QPushButton)
    for c in button_box_children:
        # TODO: Why does the assertion below not work?
        # assert 44 == c.height()  # 40px + 4px of border
        assert c.font().family() == "Montserrat"
        assert QFont.DemiBold - 1 == c.font().weight()
        assert c.font().pixelSize() == 15
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
    assert print_dialog.minimumSize().width() == 800
    assert print_dialog.maximumSize().width() == 800
    assert print_dialog.minimumSize().height() == 300
    assert print_dialog.maximumSize().height() == 800
    assert print_dialog.palette().color(QPalette.Background).name() == "#ffffff"
    assert print_dialog.header_icon.minimumSize().width() == 110  # 80px + 30px margin
    assert print_dialog.header_icon.maximumSize().width() == 110  # 80px + 30px margin
    assert print_dialog.header_icon.minimumSize().height() == 64  # 64px + 0px margin
    assert print_dialog.header_icon.maximumSize().height() == 64  # 64px + 0px margin
    assert print_dialog.header_spinner_label.minimumSize().width() == 110  # 80px + 30px margin
    assert print_dialog.header_spinner_label.maximumSize().width() == 110  # 80px + 30px margin
    assert print_dialog.header_spinner_label.minimumSize().height() == 64  # 64px + 0px margin
    assert print_dialog.header_spinner_label.maximumSize().height() == 64  # 64px + 0px margin
    assert print_dialog.header.minimumSize().height() == 68  # 68px + 0px margin
    assert print_dialog.header.maximumSize().height() == 68  # 68px + 0px margin
    assert print_dialog.header.font().family() == "Montserrat"
    assert QFont.Bold == print_dialog.header.font().weight()
    assert print_dialog.header.font().pixelSize() == 24
    assert print_dialog.header.palette().color(QPalette.Foreground).name() == "#2a319d"
    assert print_dialog.header.getContentsMargins() == (0, 0, 0, 0)
    assert print_dialog.header_line.minimumSize().height() == 2  # 2px + 20px margin
    assert print_dialog.header_line.maximumSize().height() == 2  # 2px + 20px margin
    assert math.floor(255 * 0.15) == 38  # sanity check
    assert print_dialog.header_line.palette().color(QPalette.Background).rgba64().alpha8() == 38
    assert print_dialog.header_line.palette().color(QPalette.Background).red() == 42
    assert print_dialog.header_line.palette().color(QPalette.Background).green() == 49
    assert print_dialog.header_line.palette().color(QPalette.Background).blue() == 157

    assert print_dialog.body.font().family() == "Montserrat"
    assert print_dialog.body.font().pixelSize() == 16
    assert print_dialog.body.palette().color(QPalette.Foreground).name() == "#302aa3"
    window_buttons = print_dialog.layout().itemAt(4).widget()
    button_box = window_buttons.layout().itemAt(0).widget()
    button_box_children = button_box.findChildren(QPushButton)
    for c in button_box_children:
        assert c.font().family() == "Montserrat"
        assert QFont.DemiBold - 1 == c.font().weight()
        assert c.font().pixelSize() == 15


def test_styles_for_export_file_wizard(export_file_wizard):
    assert export_file_wizard.minimumSize().width() == 800
    assert export_file_wizard.maximumSize().width() == 800
    assert export_file_wizard.minimumSize().height() == 500
    assert export_file_wizard.maximumSize().height() == 800
    assert export_file_wizard.palette().color(QPalette.Background).name() == "#ffffff"

    buttons = [
        export_file_wizard.next_button,
        export_file_wizard.back_button,
        export_file_wizard.finish_button,
        export_file_wizard.cancel_button,
    ]

    for c in buttons:
        assert c.height() == 40
        assert c.font().family() == "Montserrat"
        assert QFont.DemiBold - 1 == c.font().weight()
        assert c.font().pixelSize() == 15


def test_styles_for_export_file_wizard_page(export_file_wizard):
    page = export_file_wizard.currentPage()
    assert isinstance(page, PreflightPage)
    assert page.palette().color(QPalette.Background).name() == "#ffffff"
    assert page.header_icon.minimumSize().width() == 110  # 80px + 30px margin
    assert page.header_icon.maximumSize().width() == 110  # 80px + 30px margin
    assert page.header_icon.minimumSize().height() == 64  # 64px + 0px margin
    assert page.header_icon.maximumSize().height() == 64  # 64px + 0px margin
    assert page.header_spinner_label.minimumSize().width() == 110  # 80px + 30px margin
    assert page.header_spinner_label.maximumSize().width() == 110  # 80px + 30px margin
    assert page.header_spinner_label.minimumSize().height() == 64  # 64px + 0px margin
    assert page.header_spinner_label.maximumSize().height() == 64  # 64px + 0px margin
    assert page.header.minimumSize().height() == 68  # 68px + 0px margin
    assert page.header.maximumSize().height() == 68  # 68px + 0px margin
    assert page.header.font().family() == "Montserrat"
    assert QFont.Bold == page.header.font().weight()
    assert page.header.font().pixelSize() == 24
    assert page.header.palette().color(QPalette.Foreground).name() == "#2a319d"
    assert page.header.getContentsMargins() == (0, 0, 0, 0)
    assert page.header_line.minimumSize().height() == 2  # 2px + 20px margin
    assert page.header_line.maximumSize().height() == 2  # 2px + 20px margin
    assert math.floor(255 * 0.15) == 38  # sanity check
    assert page.header_line.palette().color(QPalette.Background).rgba64().alpha8() == 38
    assert page.header_line.palette().color(QPalette.Background).red() == 42
    assert page.header_line.palette().color(QPalette.Background).green() == 49
    assert page.header_line.palette().color(QPalette.Background).blue() == 157

    assert page.body.font().family() == "Montserrat"
    assert page.body.font().pixelSize() == 16
    assert page.body.palette().color(QPalette.Foreground).name() == "#302aa3"


def test_style_passphrase_wizard_page(export_file_wizard):
    page = export_file_wizard.currentPage()
    assert isinstance(page, PreflightPage)
    export_file_wizard.next()

    # The mock_export fixture starts with a device inserted, so the next page will be
    # the passphrase prompt
    page = export_file_wizard.currentPage()
    assert isinstance(page, PassphraseWizardPage)

    form_children_qlineedit = page.passphrase_form.findChildren(QLineEdit)
    for c in form_children_qlineedit:
        assert c.palette().color(QPalette.Background).name() == "#f8f8f8"
        assert c.minimumSize().height() == 32  # 30px + 2px padding-bottom
        assert c.maximumSize().height() == 32  # 30px + 2px padding-bottom

    passphrase_children_qlabel = page.passphrase_form.findChildren(QLabel)
    for c in passphrase_children_qlabel:
        assert c.font().family() == "Montserrat" or c.font().family() == "Source Sans Pro"
        assert c.palette().color(QPalette.Foreground).name() == "#2a319d"
        assert c.font().pixelSize() == 12
        assert QFont.DemiBold - 1 == c.font().weight()
