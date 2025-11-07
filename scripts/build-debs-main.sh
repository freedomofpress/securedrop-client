#!/bin/bash
set -euxo pipefail
# Build packages. This runs *inside* the container.

export PIP_DISABLE_PIP_VERSION_CHECK=1
export PIP_PROGRESS_BAR=off
export CARGO_TERM_COLOR=never
export CARGO_TERM_PROGRESS_WHEN=never

# Set BUILD_APP=true if WHAT=app
if [ "${WHAT:-}" = "app" ]; then
    export BUILD_APP=true
fi

# Update container
apt-get update && apt-get upgrade --yes

# Make a copy of the source tree since we do destructive operations on it
rsync --exclude=build --exclude=.git --exclude=__pycache__ --exclude=node_modules --exclude=target \
    --exclude=htmlcov --exclude=app/dist --exclude=app/out \
    -av /src/ /srv/securedrop-client
cd /srv/securedrop-client

# Conditionally add app package if BUILD_APP is set (must be done before apt-get build-dep)
if [ "${BUILD_APP:-}" = "true" ]; then
    echo "BUILD_APP is set to 'true', adding securedrop-app package to debian/control"
    bash ./debian/add-app-package.sh
fi

apt-get build-dep . --yes

# Tweak the changelog just a bit
./scripts/fixup-changelog.sh

dpkg-buildpackage --no-sign
ls ../
# Copy the built artifacts back and print checksums
mv -v ../*.{buildinfo,changes,deb,dsc,tar.gz} /build/
cd /build/
sha256sum ./*
