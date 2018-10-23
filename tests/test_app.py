"""
Tests for the app module, which sets things up and runs the application.
"""
import os
import pytest
import sys
from PyQt5.QtWidgets import QApplication
from unittest import mock
from securedrop_client.app import ENCODING, excepthook, configure_logging, \
    start_app, arg_parser, DEFAULT_SDC_HOME, run, configure_signal_handlers


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


def test_configure_logging(safe_tmpdir):
    """
    Ensure logging directory is created and logging is configured in the
    expected (rotating logs) manner.
    """
    with mock.patch('securedrop_client.app.TimedRotatingFileHandler') as \
            log_conf, \
            mock.patch('securedrop_client.app.os.path.exists',
                       return_value=False), \
            mock.patch('securedrop_client.app.logging') as logging:
        log_file = safe_tmpdir.mkdir('logs').join('client.log')
        configure_logging(str(safe_tmpdir))
        log_conf.assert_called_once_with(log_file, when='midnight',
                                         backupCount=5, delay=0,
                                         encoding=ENCODING)
        logging.getLogger.assert_called_once_with()
        assert sys.excepthook == excepthook


def test_start_app(safe_tmpdir):
    """
    Ensure the expected things are configured and the application is started.
    """
    mock_session_class = mock.MagicMock()
    mock_args = mock.MagicMock()
    mock_qt_args = mock.MagicMock()
    sdc_home = str(safe_tmpdir)
    mock_args.sdc_home = sdc_home

    with mock.patch('securedrop_client.app.configure_logging') as conf_log, \
            mock.patch('securedrop_client.app.QApplication') as mock_app, \
            mock.patch('securedrop_client.app.Window') as mock_win, \
            mock.patch('securedrop_client.app.Client') as mock_client, \
            mock.patch('securedrop_client.app.sys') as mock_sys, \
            mock.patch('securedrop_client.app.sessionmaker',
                       return_value=mock_session_class):
        start_app(mock_args, mock_qt_args)
        mock_app.assert_called_once_with(mock_qt_args)
        mock_win.assert_called_once_with()
        mock_client.assert_called_once_with('http://localhost:8081/',
                                            mock_win(), mock_session_class(),
                                            sdc_home)


PERMISSIONS_CASES = [
    {
        'should_pass': True,
        'home_perms': None,
        'sub_dirs': [],
    },
    {
        'should_pass': True,
        'home_perms': 0o0700,
        'sub_dirs': [],
    },
    {
        'should_pass': False,
        'home_perms': 0o0740,
        'sub_dirs': [],
    },
    {
        'should_pass': False,
        'home_perms': 0o0704,
        'sub_dirs': [],
    },
    {
        'should_pass': True,
        'home_perms': 0o0700,
        'sub_dirs': [('logs', 0o0700)],
    },
    {
        'should_pass': False,
        'home_perms': 0o0700,
        'sub_dirs': [('logs', 0o0740)],
    },
]


def test_create_app_dir_permissions(tmpdir):
    mock_session_class = mock.MagicMock()
    mock_args = mock.MagicMock()
    mock_qt_args = mock.MagicMock()

    for idx, case in enumerate(PERMISSIONS_CASES):
        sdc_home = os.path.join(str(tmpdir), 'case-{}'.format(idx))

        # optionally create the dir
        if case['home_perms'] is not None:
            os.mkdir(sdc_home, case['home_perms'])

        mock_args.sdc_home = sdc_home

        for subdir, perms in case['sub_dirs']:
            full_path = os.path.join(sdc_home, subdir)
            os.makedirs(full_path, perms)

        with mock.patch('logging.getLogger'), \
                mock.patch('securedrop_client.app.QApplication') as mock_app, \
                mock.patch('securedrop_client.app.Window') as mock_win, \
                mock.patch('securedrop_client.app.Client') as mock_client, \
                mock.patch('securedrop_client.app.sys') as mock_sys, \
                mock.patch('securedrop_client.app.sessionmaker',
                           return_value=mock_session_class):

            def func():
                start_app(mock_args, mock_qt_args)

            if case['should_pass']:
                func()
            else:
                with pytest.raises(RuntimeError):
                    func()


def test_argparse():
    parser = arg_parser()

    return_value = '/some/path'
    with mock.patch('os.path.expanduser', return_value=return_value) \
            as mock_expand:
        args = parser.parse_args([])

    # check that the default home is used when no args args supplied
    mock_expand.assert_called_once_with(DEFAULT_SDC_HOME)
    # check that sdc_home is set after parsing args
    assert args.sdc_home == return_value


def test_main():
    with mock.patch('securedrop_client.app.run') as mock_run:
        import securedrop_client.__main__  # noqa

    assert mock_run.called


def test_run():
    mock_args = mock.MagicMock()
    mock_qt_args = []

    def fake_known_args():
        return (mock_args, mock_qt_args)

    with mock.patch('securedrop_client.app.start_app') as mock_start_app, \
            mock.patch('argparse.ArgumentParser.parse_known_args',
                       side_effect=fake_known_args) as wat:
        run()

        mock_start_app.assert_called_once_with(mock_args, mock_qt_args)


def test_signal_interception():
    # check that initializing an app calls configure_signal_handlers
    with mock.patch('securedrop_client.app.QApplication'), \
            mock.patch('sys.exit'), \
            mock.patch('securedrop_client.models.make_engine'), \
            mock.patch('securedrop_client.app.init'), \
            mock.patch('securedrop_client.logic.Client.setup'), \
            mock.patch('securedrop_client.app.configure_logging'), \
            mock.patch('securedrop_client.app.configure_signal_handlers') \
            as mock_signal_handlers:
        start_app(mock.MagicMock(), [])
    assert mock_signal_handlers.called

    # check that a signal interception calls quit on the app
    mock_app = mock.MagicMock()
    with mock.patch.object(mock_app, 'quit') as mock_quit, \
            mock.patch('signal.signal') as mock_signal:
        configure_signal_handlers(mock_app)
        assert mock_signal.called

        assert not mock_quit.called
        signal_handler = mock_signal.call_args_list[0][0][1]
        signal_handler()
        assert mock_quit.called
