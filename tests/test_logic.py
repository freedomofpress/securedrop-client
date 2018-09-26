"""
Make sure the Client object, containing the application logic, behaves as
expected.
"""
from securedrop_client.logic import Client
from unittest import mock


def test_Client_init():
    """
    The passed in gui, app and session instances are correctly referenced and,
    where appropriate, have a reference back to the client.
    """
    mock_gui = mock.MagicMock()
    mock_api = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client(mock_gui, mock_api, mock_session)
    assert cl.gui == mock_gui
    assert cl.api == mock_api
    assert cl.session == mock_session
    assert cl.gui.controller == cl


def test_Client_setup():
    """
    Ensure the application is set up with the following default state:
    """
    mock_gui = mock.MagicMock()
    mock_api = mock.MagicMock()
    mock_session = mock.MagicMock()
    cl = Client(mock_gui, mock_api, mock_session)
    cl.setup()
    cl.gui.show_login.assert_called_once_with()
    assert cl.gui.show_sources.call_count == 1
