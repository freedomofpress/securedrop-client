#!/bin/sh

# Conditional Split-GPG prompt dismissal
# NOTE: unnecessary when overriding can be done via vm-config
#       https://github.com/QubesOS/qubes-issues/issues/10640
if [ -e "/var/run/qubes-service/securedrop-gpg-dismiss-prompt" ]; then

    # hides GPG prompt (trick: max epoch)
    export QUBES_GPG_AUTOACCEPT=2147483647

    # reset ~/.profile to remove lingering QUBES_GPG_AUTOACCEPT override
    cat /etc/skel/.profile > /rw/home/user/.profile
fi
