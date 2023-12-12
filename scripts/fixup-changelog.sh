#!/bin/bash
set -euxo pipefail
# Adjust d/changelog version to suffix the codename.
# This runs *inside* the container.

source /etc/os-release
if [[ "$VERSION_CODENAME" == "" ]]; then
    # PRETTY_NAME="Debian GNU/Linux bookworm/sid"
    # Use awk to split on spaces and /
    VERSION_CODENAME=$(echo $PRETTY_NAME | awk '{split($0, a, "[ /]"); print a[4]}')
fi

version=$(dpkg-parsechangelog -S Version)
sed -i "0,/${version}/ s//${version}+${VERSION_CODENAME}/" debian/changelog
