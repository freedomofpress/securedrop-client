"""
Make sure the UI widgets are configured correctly and work as expected.
"""
from PyQt5.QtWidgets import QLineEdit, QWidget
from securedrop_client.gui.widgets import (ToolBar, MainView, SourceList,
                                           SourceWidget, LoginView)
from unittest import mock


def test_ToolBar_init():
    """
    Ensure the ToolBar instance is correctly set up.
    """
    tb = ToolBar(None)
    assert "Synchronized: " in tb.status.text()


def test_MainView_init():
    """
    Ensure the MainView instance is correctly set up.
    """
    mv = MainView(None)
    assert isinstance(mv.source_list, SourceList)
    assert isinstance(mv.filter_term, QLineEdit)
    assert isinstance(mv.view_holder, QWidget)


def test_MainView_update_view():
    """
    Ensure the passed-in widget is added to the layout of the main view holder
    (i.e. that area of the screen on the right hand side).
    """
    mv = MainView(None)
    mv.view_holder = mock.MagicMock()
    mock_layout = mock.MagicMock()
    mock_widget = mock.MagicMock()
    with mock.patch('securedrop_client.gui.widgets.QVBoxLayout', mock_layout):
        mv.update_view(mock_widget)
        mv.view_holder.setLayout.assert_called_once_with(mock_layout())
        mock_layout().addWidget.assert_called_once_with(mock_widget)


def test_SourceList_update():
    """
    Check the items in the source list are cleared and a new SourceWidget for
    each passed-in source is created along with an associated QListWidgetItem.
    """
    sl = SourceList()
    sl.clear = mock.MagicMock()
    sl.addItem = mock.MagicMock()
    sl.setItemWidget = mock.MagicMock()
    mock_sw = mock.MagicMock()
    mock_lwi = mock.MagicMock()
    with mock.patch('securedrop_client.gui.widgets.SourceWidget', mock_sw), \
            mock.patch('securedrop_client.gui.widgets.QListWidgetItem',
                       mock_lwi):
        sources = ['a', 'b', 'c', ]
        sl.update(sources)
        sl.clear.assert_called_once_with()
        assert mock_sw.call_count == len(sources)
        assert mock_lwi.call_count == len(sources)
        assert sl.addItem.call_count == len(sources)
        assert sl.setItemWidget.call_count == len(sources)


def test_SourceWidget_init():
    """
    The source widget is initialised with the passed-in source.
    """
    sw = SourceWidget('foo', None)
    assert sw.source == 'foo'


def test_SourceWidget_update():
    """
    Ensure the widget displays the expected details from the source.
    """
    sw = SourceWidget('foo', None)
    sw.name = mock.MagicMock()
    sw.update()
    sw.name.setText.assert_called_once_with('foo')


def test_LoginView_init():
    """
    The LoginView is correctly initialised.
    """
    lv = LoginView(None)
    assert lv.title.text() == '<h1>Sign In</h1>'
