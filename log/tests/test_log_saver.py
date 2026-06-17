import builtins
import errno
import os
from pathlib import Path
from unittest import mock

import fakeredis
import pytest
from log_server import log_saver

HOME = "/home/tester"


# A sentinel exception used to break out of log_saver's `while True` loop.
# KeyboardInterrupt is a BaseException, so it is NOT swallowed by the bare
# `except Exception` in main(); this lets us stop the loop without exercising
# the error/cleanup branch.
class _StopLoop(KeyboardInterrupt):
    pass


@pytest.fixture
def home(fs):
    # The `fs` fixture (from pyfakefs) replaces the real filesystem, so nothing
    # is written to the developer's real ~/QubesIncomingLogs.
    fs.create_dir(HOME)
    with mock.patch.dict("os.environ", {"HOME": HOME}):
        yield HOME


def _client(messages):
    """A real fakeredis client preloaded with the given "vm::msg" payloads.

    main()'s `while True` loop calls blpop() with no timeout, which blocks
    forever once the queue is drained (correct for the daemon, fatal for a
    test). So we let blpop pop messages for real and only raise _StopLoop in
    place of that final block, to end the loop."""
    client = fakeredis.FakeStrictRedis()
    for m in messages:
        client.rpush("syslogmsg", m)

    real_blpop = client.blpop

    def blpop(key, timeout=0):
        if client.llen(key) == 0:
            raise _StopLoop()
        return real_blpop(key, timeout)

    client.blpop = blpop
    return client


def _logpath(vmname) -> Path:
    return Path(HOME) / "QubesIncomingLogs" / vmname / "syslog.log"


def _run(client):
    with mock.patch("redis.Redis", return_value=client), pytest.raises(_StopLoop):
        log_saver.main()


@pytest.mark.parametrize(
    ("messages", "vmname", "expected"),
    [
        # a single message is written to the VM's logfile with a trailing \n
        ([b"workvm::hello world"], "workvm", "hello world\n"),
        # only the first "::" separates vmname from the message body
        ([b"workvm::key=a::b"], "workvm", "key=a::b\n"),
        # multiple messages from one VM are appended in order
        ([b"vm1::line one", b"vm1::line two"], "vm1", "line one\nline two\n"),
    ],
)
def test_writes_messages_to_per_vm_logfile(home, messages, vmname, expected):
    _run(_client(messages))
    path = _logpath(vmname)
    assert path.exists()
    assert path.read_text() == expected


def test_multiple_vms_get_separate_files(home):
    _run(_client([b"vm1::from one", b"vm2::from two"]))
    assert _logpath("vm1").read_text() == "from one\n"
    assert _logpath("vm2").read_text() == "from two\n"


def test_file_handle_is_cached_per_vm(home):
    real_open = builtins.open
    opened = []

    def counting_open(path, *args, **kwargs):
        opened.append(path)
        return real_open(path, *args, **kwargs)

    with mock.patch("builtins.open", side_effect=counting_open):
        _run(_client([b"vm1::line one", b"vm1::line two"]))

    # Two messages from the same VM must only open the logfile once.
    assert opened.count(str(_logpath("vm1"))) == 1


def test_existing_log_directory_is_tolerated(fs, home):
    fs.create_dir(os.path.dirname(_logpath("workvm")))
    _run(_client([b"workvm::hi"]))
    assert _logpath("workvm").read_text() == "hi\n"


def test_unexpected_makedirs_error_causes_exit(home):
    with (
        mock.patch("redis.Redis", return_value=_client([b"workvm::hi"])),
        mock.patch("os.makedirs", side_effect=OSError(errno.EACCES, "denied")),
        pytest.raises(SystemExit) as exc,
    ):
        # A non-EEXIST OSError is re-raised, caught by main()'s `except
        # Exception`, and turned into a clean exit(1).
        log_saver.main()
    assert exc.value.code == 1
