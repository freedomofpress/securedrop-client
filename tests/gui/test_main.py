"""
Check the core Window UI class works as expected.
"""
from PyQt5.QtWidgets import QApplication, QVBoxLayout
from securedrop_client.gui.main import Window
from securedrop_client.gui.widgets import LoginView
from securedrop_client.resources import load_icon
from unittest import mock


app = QApplication([])


def test_init():
    """
    Ensure the Window instance is setup in the expected manner.
    """
    mock_li = mock.MagicMock(return_value=load_icon('icon.png'))
    mock_lo = mock.MagicMock(return_value=QVBoxLayout())
    mock_lo().addWidget = mock.MagicMock()
    with mock.patch('securedrop_client.gui.main.load_icon', mock_li), \
            mock.patch('securedrop_client.gui.main.ToolBar') as mock_tb, \
            mock.patch('securedrop_client.gui.main.MainView') as mock_mv, \
            mock.patch('securedrop_client.gui.main.QVBoxLayout', mock_lo), \
            mock.patch('securedrop_client.gui.main.QMainWindow') as mock_qmw:
        w = Window()
        mock_li.assert_called_once_with(w.icon)
        mock_tb.assert_called_once_with(w.widget)
        mock_mv.assert_called_once_with(w.widget)
        assert mock_lo().addWidget.call_count == 2


def test_setup():
    """
    Ensure the passed in controller is referenced and the various views are
    instantiated as expected.
    """
    w = Window()
    mock_controller = mock.MagicMock()
    w.setup(mock_controller)
    assert w.controller == mock_controller
    assert isinstance(w.login_view, LoginView)


def test_autosize_window():
    """
    Check the autosizing fits to the full screen size.
    """
    w = Window()
    w.resize = mock.MagicMock()
    mock_screen = mock.MagicMock()
    mock_screen.width.return_value = 1024
    mock_screen.height.return_value = 768
    mock_sg = mock.MagicMock()
    mock_sg.screenGeometry.return_value = mock_screen
    mock_qdw = mock.MagicMock(return_value=mock_sg)
    with mock.patch('securedrop_client.gui.main.QDesktopWidget', mock_qdw):
        w.autosize_window()
    w.resize.assert_called_once_with(1024, 768)


def test_show_login():
    """
    Ensures the update_view is called with a LoginView instance.
    """
    mock_controller = mock.MagicMock()
    w = Window()
    w.setup(mock_controller)
    w.login_view = mock.MagicMock()
    w.main_view = mock.MagicMock()
    w.show_login("error message")
    w.login_view.reset.assert_called_once_with()
    w.login_view.error.assert_called_once_with("error message")
    w.main_view.update_view.assert_called_once_with(w.login_view)


def test_show_sources():
    """
    Ensure the sources list is passed to the source list widget to be updated.
    """
    w = Window()
    w.main_view = mock.MagicMock()
    w.show_sources([1, 2, 3])
    w.main_view.source_list.update.assert_called_once_with([1, 2, 3])
