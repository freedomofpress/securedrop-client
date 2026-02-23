#!/bin/bash
# Fetches keyring from dom0 (on boot)
/usr/bin/qrexec-client-vm dom0 securedrop.GetSecretKeys /usr/bin/gpg --import -
