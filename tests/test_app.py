"""
Tests for the app module, which sets things up and runs the application.
"""
import os
import platform
import sys

import pytest

from securedrop_client import export, state
from securedrop_client.app import (
    DEFAULT_SDC_HOME,
    ENCODING,
    arg_parser,
    configure_locale_and_language,
    configure_logging,
    configure_signal_handlers,
    excepthook,
    prevent_second_instance,
    run,
    start_app,
)
from tests.helper import app  # noqa: F401


def test_application_sets_en_as_default_language_code(mocker):
    mocker.patch("locale.getdefaultlocale", return_value=(None, None))
    language_code = configure_locale_and_language()
    assert language_code == "en"


@pytest.mark.parametrize("lang", ["es"], indirect=True)
def test_application_uses_set_locale(mocker, lang):
    """
    The application respects the locale set in the environment's $LANG.
    """
    language_code = os.environ["LANG"]
    assert language_code == lang


def test_excepthook(mocker):
    """
    Ensure the custom excepthook logs the error and calls sys.exit.
    """
    ex = Exception("BANG!")
    exc_args = (type(ex), ex, ex.__traceback__)

    mock_error = mocker.patch("securedrop_client.app.logging.error")
    mock_exit = mocker.patch("securedrop_client.app.sys.exit")
    excepthook(*exc_args)
    mock_error.assert_called_once_with("Unrecoverable error", exc_info=exc_args)
    mock_exit.assert_called_once_with(1)


@pytest.mark.skipif(platform.system() != "Linux", reason="this test fails on mac")
def test_configure_logging(homedir, mocker):
    """
    Ensure logging directory is created and logging is configured in the
    expected (rotating logs) manner.
    """
    mock_log_conf = mocker.patch("securedrop_client.app.TimedRotatingFileHandler")
    mock_log_conf_sys = mocker.patch("securedrop_client.app.SysLogHandler")
    mock_logging = mocker.patch("securedrop_client.app.logging")
    mock_log_file = os.path.join(homedir, "logs", "client.log")
    configure_logging(homedir)
    mock_log_conf.assert_called_once_with(
        mock_log_file, when="midnight", backupCount=5, delay=0, encoding=ENCODING
    )
    mock_log_conf_sys.assert_called_once_with(address="/dev/log")
    mock_logging.getLogger.assert_called_once_with()
    assert sys.excepthook == excepthook


@pytest.mark.skipif(
    platform.system() != "Linux", reason="concurrent app prevention skipped on non Linux"
)
class TestSecondInstancePrevention(object):
    @staticmethod
    def mock_app(mocker):
        mock_app = mocker.MagicMock()
        mock_app.applicationName = mocker.MagicMock(return_value="sd")
        return mock_app

    @staticmethod
    def socket_mock_generator(mocker, already_bound_errno=98):
        namespace = set()

        def kernel_bind(addr):
            if addr in namespace:
                error = OSError()
                error.errno = already_bound_errno
                raise error
            else:
                namespace.add(addr)

        socket_mock = mocker.MagicMock()
        socket_mock.socket().bind = mocker.MagicMock(side_effect=kernel_bind)
        return socket_mock

    def test_diff_name(self, mocker):
        mock_exit = mocker.patch("securedrop_client.app.sys.exit")
        mocker.patch("securedrop_client.app.QMessageBox")
        mock_socket = self.socket_mock_generator(mocker)
        mock_app = self.mock_app(mocker)
        mocker.patch("securedrop_client.app.socket", new=mock_socket)
        prevent_second_instance(mock_app, "name1")
        prevent_second_instance(mock_app, "name2")
        mock_exit.assert_not_called()

    def test_same_name(self, mocker):
        mock_exit = mocker.patch("securedrop_client.app.sys.exit")
        mocker.patch("securedrop_client.app.QMessageBox")
        mock_socket = self.socket_mock_generator(mocker)
        mock_app = self.mock_app(mocker)
        mocker.patch("securedrop_client.app.socket", new=mock_socket)
        prevent_second_instance(mock_app, "name1")
        prevent_second_instance(mock_app, "name1")
        mock_exit.assert_any_call()

    def test_unknown_kernel_error(self, mocker):
        mocker.patch("securedrop_client.app.sys.exit")
        mocker.patch("securedrop_client.app.QMessageBox")
        mock_socket = self.socket_mock_generator(mocker, 131)  # crazy unexpected error
        mock_app = self.mock_app(mocker)
        mocker.patch("securedrop_client.app.socket", new=mock_socket)
        with pytest.raises(OSError):
            prevent_second_instance(mock_app, "name1")
            prevent_second_instance(mock_app, "name1")


def test_start_app(homedir, mocker):
    """
    Ensure the expected things are configured and the application is started.
    """
    mock_session_maker = mocker.MagicMock()
    mock_args = mocker.MagicMock()
    mock_qt_args = mocker.MagicMock()
    mock_args.sdc_home = str(homedir)
    mock_args.proxy = False
    app_state = state.State()
    mocker.patch("securedrop_client.state.State", return_value=app_state)
    export_service = export.Service()
    mocker.patch("securedrop_client.export.Service", return_value=export_service)

    mocker.patch("securedrop_client.app.configure_logging")
    mock_app = mocker.patch("securedrop_client.app.QApplication")
    mock_win = mocker.patch("securedrop_client.app.Window")
    mocker.patch("securedrop_client.resources.path", return_value=mock_args.sdc_home + "dummy.jpg")
    mock_controller = mocker.patch("securedrop_client.app.Controller")
    mocker.patch("securedrop_client.app.prevent_second_instance")
    mocker.patch("securedrop_client.app.sys")
    mocker.patch("securedrop_client.app.make_session_maker", return_value=mock_session_maker)

    start_app(mock_args, mock_qt_args)

    mock_app.assert_called_once_with(mock_qt_args)
    mock_win.assert_called_once_with(app_state, export_service)
    mock_controller.assert_called_once_with(
        "http://localhost:8081/",
        mock_win(),
        mock_session_maker,
        homedir,
        app_state,
        False,
        False,
        mocker.ANY,
        mocker.ANY,
        mocker.ANY,
    )


PERMISSIONS_CASES = [
    {"should_pass": True, "home_perms": None, "sub_dirs": []},
    {"should_pass": True, "home_perms": 0o0700, "sub_dirs": []},
    {"should_pass": False, "home_perms": 0o0740, "sub_dirs": []},
    {"should_pass": False, "home_perms": 0o0704, "sub_dirs": []},
    {"should_pass": True, "home_perms": 0o0700, "sub_dirs": [("logs", 0o0700)]},
    {"should_pass": False, "home_perms": 0o0700, "sub_dirs": [("logs", 0o0740)]},
]


def test_create_app_dir_permissions(tmpdir, mocker):

    for idx, case in enumerate(PERMISSIONS_CASES):
        mock_session_maker = mocker.MagicMock()
        mock_args = mocker.MagicMock()
        sdc_home = os.path.join(str(tmpdir), "case-{}".format(idx))
        mock_args.sdc_home = sdc_home
        mock_qt_args = mocker.MagicMock()

        # optionally create the dir
        if case["home_perms"]:
            os.mkdir(sdc_home, case["home_perms"])

        mock_args.sdc_home = sdc_home

        for subdir, perms in case["sub_dirs"]:
            full_path = os.path.join(sdc_home, subdir)
            os.makedirs(full_path, perms)

        mocker.patch("logging.getLogger")
        mocker.patch("securedrop_client.app.QApplication")
        mocker.patch("securedrop_client.app.Window")
        mocker.patch("securedrop_client.app.Controller")
        mocker.patch("securedrop_client.app.sys")
        mocker.patch("securedrop_client.resources.path", return_value=sdc_home + "dummy.jpg")
        mocker.patch("securedrop_client.app.prevent_second_instance")
        mocker.patch("securedrop_client.app.make_session_maker", return_value=mock_session_maker)

        def func():
            start_app(mock_args, mock_qt_args)

        func()

        # stop all mocks before the next iteration
        mocker.stopall()


def test_argparse(mocker):
    parser = arg_parser()

    return_value = "/some/path"
    mock_expand = mocker.patch("os.path.expanduser", return_value=return_value)
    args = parser.parse_args([])

    # check that the default home is used when no args are supplied
    mock_expand.assert_called_once_with(DEFAULT_SDC_HOME)
    # check that sdc_home is set after parsing args
    assert args.sdc_home == return_value


def test_main(mocker):
    mock_run = mocker.patch("securedrop_client.app.run")
    import securedrop_client.__main__  # noqa

    assert mock_run.called


def test_run(mocker):
    mock_args = mocker.MagicMock()
    mock_qt_args = []

    def fake_known_args():
        return (mock_args, mock_qt_args)

    mock_start_app = mocker.patch("securedrop_client.app.start_app")
    mocker.patch("argparse.ArgumentParser.parse_known_args", side_effect=fake_known_args)
    run()
    mock_start_app.assert_called_once_with(mock_args, mock_qt_args)


def test_signal_interception(mocker, homedir):
    # check that initializing an app calls configure_signal_handlers
    mocker.patch("securedrop_client.app.QApplication")
    mocker.patch("securedrop_client.app.prevent_second_instance")
    mocker.patch("sys.exit")
    mocker.patch("securedrop_client.db.make_session_maker")
    mocker.patch("securedrop_client.app.Database")
    mocker.patch("securedrop_client.app.init")
    mocker.patch("securedrop_client.logic.Controller.setup")
    mocker.patch("securedrop_client.logic.GpgHelper")
    mocker.patch("securedrop_client.app.configure_logging")
    mock_signal_handlers = mocker.patch("securedrop_client.app.configure_signal_handlers")
    mock_args = mocker.Mock()
    mock_args.sdc_home = homedir

    start_app(mock_args, [])
    assert mock_signal_handlers.called

    # check that a signal interception calls quit on the app
    mock_app = mocker.MagicMock()
    mock_quit = mocker.patch.object(mock_app, "quit")
    mock_signal = mocker.patch("signal.signal")

    configure_signal_handlers(mock_app)
    assert mock_signal.called

    assert not mock_quit.called
    signal_handler = mock_signal.call_args_list[0][0][1]
    signal_handler()
    assert mock_quit.called
