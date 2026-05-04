#!/usr/bin/env python3
# Print git commit/tag info and verify signatures.
# For production release tags (no 'rc'), the tag must be signed exclusively
# by the production release key.

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


def prod_key() -> str:
    """
    Extract key from Signed-By block.
    Lines are indented with one space; empty lines in the key are ` .`
    """
    sources = Path("keyring/apt_freedom_press.sources").read_text()
    key_lines = []
    in_block = False
    for line in sources.splitlines():
        if line.startswith("Signed-By:"):
            in_block = True
            continue
        if in_block:
            if line.startswith(" "):
                content = line[1:]
                key_lines.append("" if content == "." else content)
            else:
                break
    return "\n".join(key_lines) + "\n"


print("$ git log -1 --oneline --show-signature")
subprocess.run(
    ["git", "--no-pager", "log", "-1", "--oneline", "--show-signature", "--no-color"], check=False
)

# Record if we're building with local changes present.
print("$ git status --short")
subprocess.run(["git", "status", "--short"], check=True)

all_tags = subprocess.run(
    ["git", "tag", "--points-at", "HEAD"], capture_output=True, text=True, check=False
).stdout.split()

if len(all_tags) > 1:
    print(f"ERROR: multiple tags point at HEAD: {' '.join(all_tags)}", file=sys.stderr)
    sys.exit(1)

tag = all_tags[0] if all_tags else None
if not tag:
    # No tag, we're all done
    sys.exit(0)

if "rc" in tag:
    # RC tags may be signed by a key not in the local keyring; don't fail.
    print(f"$ git tag -v {tag}")
    result = subprocess.run(["git", "--no-pager", "tag", "-v", tag], check=False)
    if result.returncode == 0:
        print(f"OK: Tag {tag} verified against local key")
    else:
        print(f"WARNING: Tag {tag} failed to verify")
    sys.exit(0)

print(f"Production release tag detected: {tag}")
print("Verifying tag is signed by production key from keyring/apt_freedom_press.sources")


tmpdir = tempfile.mkdtemp()
Path(tmpdir).chmod(0o700)
try:
    subprocess.run(
        ["gpg", "--homedir", tmpdir, "--import"], input=prod_key(), text=True, check=True
    )
    print(f"$ git tag -v {tag} # against production key")
    result = subprocess.run(
        ["git", "--no-pager", "tag", "-v", tag],
        check=False,
        env={**os.environ, "GNUPGHOME": tmpdir},
    )
    if result.returncode == 0:
        print(f"OK: Tag {tag} verified against production key")
    else:
        print(f"ERROR: Tag {tag} failed verification against production key")
        sys.exit(1)
finally:
    shutil.rmtree(tmpdir)
