"""
Tests for the app module, which sets things up and runs the application.
"""
import sys
from PyQt5.QtWidgets import QApplication
from unittest import mock
from securedrop_client.app import ENCODING, excepthook, configure_logging, \
    start_app


app = QApplication([])


def test_excpethook():
    """
    Ensure the custom excepthook logs the error and calls sys.exit.
    """
    ex = Exception('BANG!')
    exc_args = (type(ex), ex, ex.__traceback__)

    with mock.patch('securedrop_client.app.logging.error') as error, \
            mock.patch('securedrop_client.app.sys.exit') as exit:
        excepthook(*exc_args)
        error.assert_called_once_with('Unrecoverable error', exc_info=exc_args)
        exit.assert_called_once_with(1)


def test_configure_logging(tmpdir):
    """
    Ensure logging directory is created and logging is configured in the
    expected (rotating logs) manner.
    """
    with mock.patch('securedrop_client.app.TimedRotatingFileHandler') as \
            log_conf, \
            mock.patch('securedrop_client.app.os.path.exists',
                       return_value=False), \
            mock.patch('securedrop_client.app.logging') as logging:
        log_dir = str(tmpdir)
        log_file = tmpdir.join('client.log')
        configure_logging(log_dir)
        log_conf.assert_called_once_with(log_file, when='midnight',
                                         backupCount=5, delay=0,
                                         encoding=ENCODING)
        logging.getLogger.assert_called_once_with()
        assert sys.excepthook == excepthook


def test_run():
    """
    Ensure the expected things are configured and the application is started.
    """
    mock_session_class = mock.MagicMock()
    mock_args = mock.MagicMock()
    mock_qt_args = mock.MagicMock()
    with mock.patch('securedrop_client.app.configure_logging') as conf_log, \
            mock.patch('securedrop_client.app.QApplication') as mock_app, \
            mock.patch('securedrop_client.app.Window') as mock_win, \
            mock.patch('securedrop_client.app.Client') as mock_client, \
            mock.patch('securedrop_client.app.sys') as mock_sys, \
            mock.patch('securedrop_client.app.init') as mock_init, \
            mock.patch('securedrop_client.app.sessionmaker',
                       return_value=mock_session_class):
        start_app(mock_args, mock_qt_args)
        mock_app.assert_called_once_with(mock_qt_args)
        mock_win.assert_called_once_with()
        mock_client.assert_called_once_with('http://localhost:8081/',
                                            mock_win(), mock_session_class())
