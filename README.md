# OQubes Logging

This is a PoC logging service based on [Qubes
buildlog](https://github.com/QubesOS/qubes-builder/blob/master/rpc-services/qubesbuilder.BuildLog).

## How to use/try this?

In our example, we will use a vm named *logging* for storing logs, and we will use 
*workvm* to send in logs to the *logging* vm.

### In dom0

- Create a file `/etc/qubes-rpc/policy/oqubes.Logging` in `dom0` with the following content.

```
workvm logging allow
@anyvm @anyvm deny
```

### In logging vm

Add the following content to `/etc/qubes-rpc/oqubes.Logging`

```
/usr/sbin/oqubes-logging
```

and then place `oqubes-logging` script to `/usr/sbin/` directory and make sure that
it is executable.

### To use from any Python code in workvm

Here is an example code using Python logging

```Python
import logging
from oqubeslogging import OQubesLog

def main():
    handler = OQubesLog("workvm", "proxy-debian")
    logging.basicConfig(level=logging.DEBUG, handlers=[handler])
    logger = logging.getLogger("example")

    logger.info("kushal says it works")


if __name__ == "__main__":
    main()

```

## The journalctl example

TODO: add an example of streaming journalctl logs via python code.