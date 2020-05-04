from PyQt5.QtCore import QTimer
from PyQt5.QtGui import QFont, QPalette
from PyQt5.QtWidgets import QApplication, QLabel, QWidget

from securedrop_client import logic
from securedrop_client.app import start_app
from securedrop_client.gui.main import Window


app = QApplication([])


def test_class_name_matches_css_object_name(homedir, mocker):
    mock_args = mocker.MagicMock()
    mock_qt_args = []
    mock_args.sdc_home = str(homedir)
    mock_args.proxy = False
    gui = Window()
    controller = logic.Controller('http://localhost', gui, mocker.MagicMock(), homedir)
    mocker.patch('securedrop_client.app.QApplication', return_value=app)
    mocker.patch('securedrop_client.app.Controller', return_value=controller)
    mocker.patch('securedrop_client.app.sys.exit')
    timer = QTimer()
    timer.start(500)
    timer.timeout.connect(app.exit)

    start_app(mock_args, mock_qt_args)

    sync_icon = gui.top_pane.sync_icon
    assert 'SyncIcon' == sync_icon.__class__.__name__
    assert 'SyncIcon' == sync_icon.objectName()
    activity_status_bar = gui.top_pane.activity_status_bar
    assert 'ActivityStatusBar' == activity_status_bar.__class__.__name__
    assert 'ActivityStatusBar' == activity_status_bar.objectName()
    error_status_bar = gui.top_pane.error_status_bar
    assert 'ErrorStatusBar' == error_status_bar.__class__.__name__
    assert 'ErrorStatusBar' in error_status_bar.vertical_bar.objectName()
    assert 'ErrorStatusBar' in error_status_bar.label.objectName()
    assert 'ErrorStatusBar' in error_status_bar.status_bar.objectName()
    user_profile = gui.left_pane.user_profile
    assert 'UserProfile' == user_profile.__class__.__name__
    assert 'UserProfile' == user_profile.objectName()
    assert 'UserProfile' in user_profile.user_icon.objectName()
    user_button = user_profile.user_button
    assert 'UserButton' == user_button.__class__.__name__
    assert 'UserButton' == user_button.objectName()
    login_button = user_profile.login_button
    assert 'LoginButton' == login_button.__class__.__name__
    assert 'LoginButton' == login_button.objectName()
    main_view = gui.main_view
    assert 'MainView' == main_view.__class__.__name__
    assert 'MainView' == main_view.objectName()
    assert 'MainView' in main_view.view_holder.objectName()
    empty_conversation_view = main_view.empty_conversation_view
    'EmptyConversationView' == empty_conversation_view.__class__.__name__
    'EmptyConversationView' == empty_conversation_view.objectName()
    'EmptyConversationView' in empty_conversation_view.no_sources.objectName()
    'EmptyConversationView' in empty_conversation_view.no_source_selected.objectName()


def test_styles(homedir, mocker):
    mock_args = mocker.MagicMock()
    mock_qt_args = []
    mock_args.sdc_home = str(homedir)
    mock_args.proxy = False
    gui = Window()
    controller = logic.Controller('http://localhost', gui, mocker.MagicMock(), homedir)
    mocker.patch('securedrop_client.app.QApplication', return_value=app)
    mocker.patch('securedrop_client.app.Controller', return_value=controller)
    mocker.patch('securedrop_client.app.sys.exit')
    timer = QTimer()
    timer.start(500)
    timer.timeout.connect(app.exit)

    start_app(mock_args, mock_qt_args)

    sync_icon = gui.top_pane.sync_icon
    assert '#ffffff' == sync_icon.palette().color(QPalette.Base).name()
    # TODO: Add test for 'border: none;'

    activity_status_bar = gui.top_pane.activity_status_bar
    assert 'Source Sans Pro' == activity_status_bar.font().family()
    assert QFont.Bold == activity_status_bar.font().weight()
    assert 12 == activity_status_bar.font().pixelSize()
    assert '#ffffff' == activity_status_bar.palette().color(QPalette.Base).name()
    assert '#d3d8ea' == activity_status_bar.palette().color(QPalette.Foreground).name()

    error_status_bar = gui.top_pane.error_status_bar
    assert '#ff3366' == error_status_bar.vertical_bar.palette().color(QPalette.Background).name()
    # TODO: Add test for 'background-color: qlineargradient(...' for vertical_bar
    # TODO: Add test for 'background-color: qlineargradient(...'' for status_bar
    assert 'Source Sans Pro' == error_status_bar.status_bar.font().family()
    assert QFont.Normal == error_status_bar.status_bar.font().weight()
    assert 14 == error_status_bar.status_bar.font().pixelSize()
    assert '#0c3e75' == error_status_bar.status_bar.palette().color(QPalette.Foreground).name()

    user_profile = gui.left_pane.user_profile
    # TODO: Add test for 'padding: 15px;' for user_profile
    # TODO: Add test for 'border: none;' for user_icon
    assert '#9211ff' == user_profile.user_icon.palette().color(QPalette.Background).name()
    # TODO: Add test for 'padding-left: 3px;' for user_icon
    # TODO: Add test for 'padding-bottom: 4px;' for user_icon
    assert 'Source Sans Pro' == user_profile.user_icon.font().family()
    assert QFont.Bold == user_profile.user_icon.font().weight()
    assert 15 == user_profile.user_icon.font().pixelSize()
    assert '#ffffff' == user_profile.user_icon.palette().color(QPalette.Foreground).name()

    user_button = user_profile.user_button
    # TODO: Add test for 'border: none;'
    assert 'Source Sans Pro' == user_button.font().family()
    assert QFont.Black == user_button.font().weight()
    assert 12 == user_button.font().pixelSize()
    assert '#ffffff' == user_button.palette().color(QPalette.Foreground).name()
    # TODO: Add test for 'text-align: left;'
    # TODO: Add test for 'outline: none;' for focus
    # TODO: Add test for 'image: none;' for menu-indicator

    login_button = user_profile.login_button
    # TODO: Add test for 'border: none;'
    assert '#05edfe' == login_button.palette().color(QPalette.Background).name()
    assert 'Montserrat' == login_button.font().family()
    assert QFont.Bold == login_button.font().weight()
    assert 14 == login_button.font().pixelSize()
    assert '#2a319d' == login_button.palette().color(QPalette.Foreground).name()
    # TODO: Add test for 'background-color: #85f6fe;' for pressed

    main_view = gui.main_view
    assert 558 == main_view.height()
    assert 667 == main_view.view_holder.width()
    # TODO: Add test for 'border: none;'
    assert '#f3f5f9' == main_view.view_holder.palette().color(QPalette.Background).name()

    no_sources = main_view.empty_conversation_view.no_sources
    assert 5 == no_sources.layout().count()
    no_sources_instructions = no_sources.layout().itemAt(0).widget()
    assert 'Montserrat' == no_sources_instructions.font().family()
    # TODO: Figure out why font size is QFont.DemiBold - 1
    # assert QFont.DemiBold - 1 == no_sources_instructions.font().weight()
    assert 35 == no_sources_instructions.font().pixelSize()
    assert '#a5b3e9' == no_sources_instructions.palette().color(QPalette.Foreground).name()
    assert 520 == no_sources_instructions.minimumWidth()
    assert 600 == no_sources_instructions.maximumWidth()
    no_sources_spacer1 = no_sources.layout().itemAt(1)
    assert 35 == no_sources_spacer1.minimumSize().height()
    assert 35 == no_sources_spacer1.maximumSize().height()
    no_sources_instruction_details1 = no_sources.layout().itemAt(2).widget()
    assert 'Montserrat' == no_sources_instruction_details1.font().family()
    assert QFont.Normal == no_sources_instruction_details1.font().weight()
    assert 35 == no_sources_instruction_details1.font().pixelSize()
    assert '#a5b3e9' == no_sources_instruction_details1.palette().color(QPalette.Foreground).name()
    no_sources_spacer2 = no_sources.layout().itemAt(3)
    assert 35 == no_sources_spacer2.minimumSize().height()
    assert 35 == no_sources_spacer2.maximumSize().height()
    no_sources_instruction_details2 = no_sources.layout().itemAt(4).widget()
    assert 'Montserrat' == no_sources_instruction_details2.font().family()
    assert QFont.Normal == no_sources_instruction_details2.font().weight()
    assert 35 == no_sources_instruction_details2.font().pixelSize()
    assert '#a5b3e9' == no_sources_instruction_details2.palette().color(QPalette.Foreground).name()

    no_source_selected = main_view.empty_conversation_view.no_source_selected
    assert 6 == no_source_selected.layout().count()
    no_source_selected_instructions = no_source_selected.layout().itemAt(0).widget()
    assert 'Montserrat' == no_source_selected_instructions.font().family()
    # TODO: Figure out why font size is QFont.DemiBold - 1
    # assert QFont.DemiBold - 1 == no_source_selected_instructions.font().weight()
    assert 35 == no_source_selected_instructions.font().pixelSize()
    assert '#a5b3e9' == no_source_selected_instructions.palette().color(QPalette.Foreground).name()
    assert 520 == no_source_selected_instructions.minimumWidth()
    assert 520 == no_source_selected_instructions.maximumWidth()
    no_source_selected_spacer1 = no_source_selected.layout().itemAt(1)
    assert 35 == no_source_selected_spacer1.minimumSize().height()
    assert 35 == no_source_selected_spacer1.maximumSize().height()
    bullet1_bullet = no_source_selected.layout().itemAt(2).widget().layout().itemAt(0).widget()
    # TODO: Add test for 'margin: 4px 0px 0px 0px;'
    35 == bullet1_bullet.font().pixelSize()
    QFont.Bold == bullet1_bullet.font().weight()
    assert 'Montserrat' == bullet1_bullet.font().family()
    assert '#a5b3e9' == bullet1_bullet.palette().color(QPalette.Foreground).name()
    bullet2_bullet = no_source_selected.layout().itemAt(3).widget().layout().itemAt(0).widget()
    # TODO: Add test for 'margin: 4px 0px 0px 0px;'
    35 == bullet2_bullet.font().pixelSize()
    QFont.Bold == bullet2_bullet.font().weight()
    assert 'Montserrat' == bullet2_bullet.font().family()
    assert '#a5b3e9' == bullet2_bullet.palette().color(QPalette.Foreground).name()
    bullet3_bullet = no_source_selected.layout().itemAt(4).widget().layout().itemAt(0).widget()
    # TODO: Add test for 'margin: 4px 0px 0px 0px;'
    35 == bullet3_bullet.font().pixelSize()
    QFont.Bold == bullet3_bullet.font().weight()
    assert 'Montserrat' == bullet3_bullet.font().family()
    assert '#a5b3e9' == bullet3_bullet.palette().color(QPalette.Foreground).name()
    no_source_selected_spacer2 = no_source_selected.layout().itemAt(5)
    assert (35 * 4) == no_source_selected_spacer2.minimumSize().height()
    assert (35 * 4) == no_source_selected_spacer2.maximumSize().height()
