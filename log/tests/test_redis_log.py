from unittest import mock

import fakeredis
import pytest
from log_server import redis_log


@pytest.mark.parametrize(
    ("untrusted", "expected"),
    [
        # printable ASCII passes through unchanged
        (b"Hello, world! 123 ~", "Hello, world! 123 ~"),
        # 0x20 (space) and 0x7E (~) are the inclusive printable boundaries
        (b"\x20\x7e", " ~"),
        # NUL, unit separator (0x1F), tab and newline are all < 0x20
        (b"a\x00b\x1fc\td\n", "a.b.c.d."),
        # 0x1F is just below the printable range, 0x7F (DEL) just above
        (b"\x1f\x7f", ".."),
        # bytes >= 0x80 must never raise UnicodeDecodeError; they become dots
        (b"\x80\xff", ".."),
        # a multi-byte UTF-8 character ("é") is two bytes, both replaced
        ("é".encode(), ".."),
        # empty input
        (b"", ""),
    ],
)
def test_sanitize_line(untrusted, expected):
    assert redis_log.sanitize_line(untrusted) == expected


@pytest.fixture
def rd():
    return fakeredis.FakeStrictRedis()


@pytest.mark.parametrize(
    ("args", "expected"),
    [
        # vmname is prefixed to the message, separated by "::"
        (("hello", "workvm"), b"workvm::hello"),
        # vmname defaults to "remote"
        (("hello",), b"remote::hello"),
        # log_saver splits on the first "::" only, so an embedded "::" is fine
        (("a::b::c", "vm"), b"vm::a::b::c"),
    ],
)
def test_log_pushes_message(rd, args, expected):
    redis_log.log(rd, *args)
    assert rd.lrange("syslogmsg", 0, -1) == [expected]


def test_log_appends_in_order(rd):
    redis_log.log(rd, "first", "vm")
    redis_log.log(rd, "second", "vm")
    assert rd.lrange("syslogmsg", 0, -1) == [b"vm::first", b"vm::second"]


def _stdin(lines):
    """A fake sys.stdin whose buffer.readline() yields the given byte strings."""
    stdin = mock.MagicMock()
    stdin.buffer.readline.side_effect = lines
    return stdin


@mock.patch.dict("os.environ", {"QREXEC_REMOTE_DOMAIN": "sourcevm"})
def test_main_reads_sanitizes_and_pushes_each_line(rd):
    with (
        mock.patch("redis.Redis", return_value=rd),
        mock.patch("sys.stdin", _stdin([b"clean line\n", b"bad\x00line\n", b""])),
    ):
        redis_log.main()
    assert rd.lrange("syslogmsg", 0, -1) == [
        b"sourcevm::clean line",
        b"sourcevm::bad.line",
    ]


@mock.patch.dict("os.environ", {"QREXEC_REMOTE_DOMAIN": "sourcevm"})
def test_main_stops_on_eof(rd):
    with (
        mock.patch("redis.Redis", return_value=rd),
        mock.patch("sys.stdin", _stdin([b""])),
    ):
        redis_log.main()
    assert rd.llen("syslogmsg") == 0


@mock.patch.dict("os.environ", {}, clear=True)
def test_main_exits_when_remote_domain_unset(rd):
    with (
        mock.patch("redis.Redis", return_value=rd),
        mock.patch("sys.stdin", _stdin([b""])),
        pytest.raises(SystemExit) as exc,
    ):
        redis_log.main()
    assert exc.value.code == 1
