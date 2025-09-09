#!/usr/bin/env python3
import os

from configure_onion_service import (
    CTOR_KEY_FILENAME,
    setup_journalist_access,
)

# File stat bit mask, used to obtain file permissions
PERM_BITMASK = 0o777


def test_setup_journalist_access(mocker, tmp_path):
    hidserv_key = "TMNSKMJYP7FYYDJNRT5ATGRMWUG34DNQOXVTEVCDVCIIRV66RUCA"
    hidserv_id = "SOME_HOSTNAME_WITHOUT_DOT_ONION"
    hidserv_hostname = f"http://{hidserv_id}.onion"
    setup_journalist_access(tmp_path, hidserv_key, hidserv_hostname)

    key_dir = tmp_path
    key_path = key_dir / CTOR_KEY_FILENAME
    # Folder isn't world-readable
    assert os.stat(key_dir).st_mode & PERM_BITMASK == 0o700
    # And the umask controlled the parent directory permissions
    assert os.stat(key_dir.parent).st_mode & PERM_BITMASK == 0o700
    # Same with the keyfile
    assert os.stat(key_path).st_mode & PERM_BITMASK == 0o600

    assert (
        key_path.read_text()
        == "SOME_HOSTNAME_WITHOUT_DOT_ONION.onion:descriptor:x25519:TMNSKMJYP7FYYDJNRT5ATGRMWUG34DNQOXVTEVCDVCIIRV66RUCA"  # noqa: E501
    )
