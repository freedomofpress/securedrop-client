#!/opt/venvs/securedrop-log/bin/python3


import os
import sys

import redis


def sanitize_line(untrusted_line):
    line = bytearray(untrusted_line)
    for i, c in enumerate(line):
        if c >= 0x20 and c <= 0x7E:
            pass
        else:
            line[i] = 0x2E
    return bytearray(line).decode("ascii")


def log(rd, msg, vmname="remote"):
    redis_msg = f"{vmname}::{msg}"
    rd.rpush("syslogmsg", redis_msg)


def main():
    stdin = sys.stdin.buffer  # python3
    rd = redis.Redis()

    # the first line is always the remote vm name
    untrusted_line = stdin.readline()
    qrexec_remote = os.getenv("QREXEC_REMOTE_DOMAIN")
    if not qrexec_remote:
        print("ERROR: QREXEC_REMOTE_DOMAIN not set", file=sys.stderr)
        sys.exit(1)

    while True:
        untrusted_line = stdin.readline()
        if untrusted_line == b"":
            break

        log(rd, sanitize_line(untrusted_line.rstrip(b"\n")), qrexec_remote)


if __name__ == "__main__":
    main()
