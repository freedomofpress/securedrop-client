# securedrop-log

This is a Python module and qrexec service for logging in Qubes for [SecureDrop](https://securedrop.org).

## How to use/try this?

In our example, we will use a vm named *logging* for storing logs, and we will use 
*workvm* to send in logs to the *logging* vm.

### In dom0

- Create a file `/etc/qubes-rpc/policy/securedrop.Log` in `dom0` with the following content.

```
workvm logging allow
@anyvm @anyvm deny
```

### In logging vm

Add the following content to `/etc/qubes-rpc/securedrop.Log`

```
/usr/sbin/securedrop-log
```

and then place `securedrop-log` script to `/usr/sbin/` directory and make sure that
it is executable.

### To use from any Python code in workvm

Here is an example code using Python logging

```Python
import logging
from securedrop_log import SecureDropLog

def main():
    handler = SecureDropLog("workvm", "proxy-debian")
    logging.basicConfig(level=logging.DEBUG, handlers=[handler])
    logger = logging.getLogger("example")

    logger.info("kushal says it works")


if __name__ == "__main__":
    main()

```

## The journalctl example

You will need `python3-systemd` package for the same.

The code is in `journal-example.py` file.