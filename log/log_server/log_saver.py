#!/opt/venvs/securedrop-log/bin/python3

import errno
import os
import sys

import redis


def main():
    rclient = redis.Redis()
    # This is the cache of open files for each vm
    openfiles = {}
    try:
        while True:
            # Wait for the next message
            qname, data = rclient.blpop("syslogmsg")
            msg = data.decode("utf-8")
            vmname, msg_str = msg.split("::", 1)

            if vmname in openfiles:
                fh = openfiles[vmname]
            else:
                # First open a file
                filepath = os.path.join(
                    os.getenv("HOME", "/"),
                    "QubesIncomingLogs",
                    f"{vmname}",  # Restricted to r"\A[0-9_.-].*\Z" by qubes.vm.validate_name()
                    "syslog.log",
                )
                dirpath = os.path.dirname(filepath)
                try:
                    os.makedirs(dirpath)
                except OSError as err:
                    if err.errno != errno.EEXIST:
                        raise
                fh = open(filepath, "a")  # noqa: SIM115

                # cache it for the next call
                openfiles[vmname] = fh

            # Now just write and flush
            fh.write(msg_str)
            fh.write("\n")
            fh.flush()
    except Exception as e:
        print(e, file=sys.stderr)
        # Clean up all open files
        for _k, v in openfiles:
            v.close()
        sys.exit(1)


if __name__ == "__main__":
    main()
