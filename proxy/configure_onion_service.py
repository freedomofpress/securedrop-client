#!/usr/bin/env python3

import base64
import os
import struct
import sys
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric import x25519

try:
    from qubesdb import QubesDB
except Exception:
    if os.environ.get("PYTEST_VERSION") is not None:
        # Running under pytest, we'll mock out QubesDB
        QubesDB = None
    else:
        # Missing and needed, fail
        raise

ARTI_KEYSTORE_PATH = Path("/var/lib/arti/.local/share/arti/keystore")
ARTI_KEY_FILENAME = "ks_hsc_desc_enc.x25519_private"

OPEN_SSH_ARMOR_TEMPLATE = (
    "-----BEGIN OPENSSH PRIVATE KEY-----\n{key_data}\n-----END OPENSSH PRIVATE KEY-----"
)


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


def convert_onion_client_key(hidserv_key):
    """
    ctor -> arti onion service discovery key conversion

    :param hidserv_key: base32-encoded secret from ctor client auth. file

    :returns: converted key
    """

    COMMENT = ""  # optional comment stored inside the key

    v = hidserv_key.strip().upper()
    v += "=" * ((8 - (len(v) % 8)) % 8)  # missing padding
    seed = base64.b32decode(v, casefold=True)

    # Clamp per RFC7748 §5 (X25519)
    k = bytearray(seed)
    k[0] &= 248
    k[31] &= 127
    k[31] |= 64
    k = bytes(k)

    # Derive public key
    try:
        pub = (
            x25519.X25519PrivateKey.from_private_bytes(k)
            .public_key()
            .public_bytes(
                encoding=serialization.Encoding.Raw, format=serialization.PublicFormat.Raw
            )
        )
    except Exception as e:
        raise SystemExit(f"Error importing key: {e}")

    ALG = b"x25519@spec.torproject.org"

    def ssh_string(b: bytes) -> bytes:
        return struct.pack(">I", len(b)) + b

    # Build the outer OpenSSH header
    magic = b"openssh-key-v1\0"
    ciphername = b"none"
    kdfname = b"none"
    kdfopts = b""
    nkeys = 1

    outer = [
        magic,
        ssh_string(ciphername),
        ssh_string(kdfname),
        ssh_string(kdfopts),
        struct.pack(">I", nkeys),
    ]

    # Public key section (one key): string( keyblob ),
    # where keyblob = string(name) + string(pubdata)
    # where pubdata is a string-wrapped 32 bytes
    pubkey_blob = ssh_string(ALG) + ssh_string(pub)
    outer.append(ssh_string(pubkey_blob))

    # Private section (unencrypted blob)
    check = os.urandom(4)
    priv_payload = bytearray()
    priv_payload += check + check  # checkint1, checkint2

    # One key:
    priv_payload += ssh_string(ALG)
    priv_payload += ssh_string(pub)  # public key data (string-wrapped 32 bytes)
    priv_payload += ssh_string(k)  # private key data (string-wrapped 32-byte scalar)
    priv_payload += ssh_string(COMMENT.encode())

    # Padding: 1..n so total is multiple of 8 bytes
    block = 8
    pad_len = (-len(priv_payload)) % block
    if pad_len:
        priv_payload += bytes(i % 256 for i in range(1, pad_len + 1))

    outer.append(ssh_string(bytes(priv_payload)))
    key_blob = b"".join(outer)

    # Write PEM-like OpenSSH key
    b64 = base64.b64encode(key_blob).decode()
    lines = [b64[i : i + 70] for i in range(0, len(b64), 70)]
    return OPEN_SSH_ARMOR_TEMPLATE.format(key_data="\n".join(lines))


def setup_journalist_access(keystore_path: Path, hidserv_key, hidserv_hostname):
    onion_service_id = (
        hidserv_hostname.removeprefix("http://").removeprefix("https://").removesuffix(".onion")
    )

    onion_service_key_dir = keystore_path / "client" / onion_service_id
    onion_service_key_path = onion_service_key_dir / ARTI_KEY_FILENAME
    umask_original = os.umask(0o077)  # This makes new dirs 700 (777 - 077 = 700)
    onion_service_key_dir.mkdir(mode=0o700, exist_ok=True, parents=True)
    os.umask(umask_original)
    onion_service_key_path.touch(mode=0o600, exist_ok=True)

    with onion_service_key_path.open("w") as key_file:
        onion_service_key = convert_onion_client_key(hidserv_key)
        key_file.write(onion_service_key)


def main():
    # Obtain credentials
    env = get_env(["SD_PROXY_ORIGIN", "SD_PROXY_ORIGIN_KEY"])
    hidserv_key = env["SD_PROXY_ORIGIN_KEY"]
    hidserv_hostname = env["SD_PROXY_ORIGIN"]

    # Authenticate
    setup_journalist_access(ARTI_KEYSTORE_PATH, hidserv_key, hidserv_hostname)


if __name__ == "__main__":
    sys.exit(main())
