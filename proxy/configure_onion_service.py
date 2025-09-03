#!/usr/bin/env python3

import os
import sys
from pathlib import Path

try:
    from qubesdb import QubesDB
except Exception:
    if os.environ.get("PYTEST_VERSION") is not None:
        # Running under pytest, we'll mock out QubesDB
        QubesDB = None
    else:
        # Missing and needed, fail
        raise

CTOR_KEYSTORE_PATH = Path("/var/lib/tor/authdir/")
CTOR_KEY_FILENAME = "app-journalist.auth_private"
CTOR_TEMPLATE = "{hidserv_hostname}:descriptor:x25519:{hidserv_key}"


def get_env(args):
    env = {}
    try:
        db = QubesDB()
        for key in args or []:
            value = db.read(f"/vm-config/{key}")
            if not value or len(value) == 0:
                raise KeyError(f"Could not read from QubesDB: {key}")
            env[key] = value.decode()

    finally:
        db.close()

    return env


def setup_journalist_access(keystore_path: Path, hidserv_key, hidserv_hostname):
    onion_service_key_dir = keystore_path
    onion_service_key_path = onion_service_key_dir / CTOR_KEY_FILENAME
    umask_original = os.umask(0o077)  # This makes new dirs 700 (777 - 077 = 700)
    onion_service_key_dir.mkdir(mode=0o700, exist_ok=True, parents=True)
    os.umask(umask_original)
    onion_service_key_path.touch(mode=0o600, exist_ok=True)

    with onion_service_key_path.open("w") as key_file:
        onion_service_key = CTOR_TEMPLATE.format(
            hidserv_hostname=hidserv_hostname.removeprefix("http://").removeprefix("https://"),
            hidserv_key=hidserv_key,
        )
        key_file.write(onion_service_key)


def main():
    # Obtain credentials
    env = get_env(["SD_PROXY_ORIGIN", "SD_PROXY_ORIGIN_KEY"])
    hidserv_key = env["SD_PROXY_ORIGIN_KEY"]
    hidserv_hostname = env["SD_PROXY_ORIGIN"]

    # Authenticate
    setup_journalist_access(CTOR_KEYSTORE_PATH, hidserv_key, hidserv_hostname)


if __name__ == "__main__":
    sys.exit(main())
