#!/bin/bash
set -euxo pipefail
# Runs inside the container
apt-get update && apt-get install --yes piuparts docker.io

# Move things in this folder so the docker build can find them
cp /keyring/apt_freedom_press.sources /piuparts
cp /scripts/qubes_42.sources /piuparts
mkdir -p /piuparts/packages
cp /build/*.deb /piuparts/packages/

cd /piuparts

docker build . --build-arg DISTRO="$DISTRO" -t ourimage

# TODO: Our currently released packages don't install with piuparts, so we pass
# --no-upgrade-test to avoid installing them and testing the upgrade path. Once
# they do we can remove that line.
piuparts --docker-image ourimage \
    --distribution "$DISTRO" \
    --warn-on-leftovers-after-purge \
    --no-upgrade-test \
    /build/securedrop-"${PACKAGE}"*.deb
