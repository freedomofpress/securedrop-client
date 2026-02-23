#!/bin/bash
# Fetches keyring from dom0 (on boot)
/usr/bin/qrexec-client-vm dom0 securedrop.GetJournalistSecretKeys /usr/bin/gpg --import -
