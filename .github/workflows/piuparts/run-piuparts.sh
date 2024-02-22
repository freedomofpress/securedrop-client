#!/bin/bash
set -euxo pipefail
# Runs inside the container
apt-get update && apt-get install --yes piuparts docker.io

cd /piuparts

cp /keyring/securedrop-keyring.gpg .
docker build . --build-arg DISTRO=$DISTRO -t ourimage

# TODO: Our currently released packages don't install with piuparts, so we pass
# --no-upgrade-test to avoid installing them and testing the upgrade path. Once
# they do we can remove that line.
piuparts --docker-image ourimage \
    --distribution $DISTRO \
    --extra-repo 'deb [signed-by=/usr/share/keyrings/securedrop-keyring.gpg] https://apt.freedom.press bullseye main' \
    --warn-on-leftovers-after-purge \
    --no-upgrade-test \
    /build/securedrop-${PACKAGE}*.deb
