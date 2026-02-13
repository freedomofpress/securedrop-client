#!/bin/bash
set -euo pipefail

# Fetches keyring from dom0 (on boot)
qrexec-client-vm dom0 securedrop.GetJournalistSecretKeys | \
    /usr/bin/gpg --import -
