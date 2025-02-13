from datetime import UTC, datetime, timedelta
from pathlib import Path

import pysequoia
from debian import deb822


def test_pgp_fingerprint_count():
    """Verify the key in the sources file is our prod signing key"""
    path = Path("apt_freedom_press.sources")

    sources = deb822.Sources(path.read_text())
    key = pysequoia.Cert.from_bytes(sources["Signed-By"].encode())
    assert key.fingerprint.upper() == "2359E6538C0613E652955E6C188EDD3B7B22E6A3"
    assert len(key.user_ids) == 1
    assert (
        str(key.user_ids[0])
        == "SecureDrop Release Signing Key <securedrop-release-key-2021@freedom.press>"
    )
    assert key.expiration.year == 2027
    # Fail if we are within 6 months of the key's expiry
    assert datetime.now(tz=UTC) < (key.expiration - timedelta(days=6 * 30)), (
        "key expires in less than 6 months"
    )
