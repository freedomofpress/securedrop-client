#!/bin/bash
set -euxo pipefail
# Build packages. This runs *inside* the container.

export PIP_DISABLE_PIP_VERSION_CHECK=1
export PIP_PROGRESS_BAR=off
export CARGO_TERM_COLOR=never
export CARGO_TERM_PROGRESS_WHEN=never

# Update container
apt-get update && apt-get upgrade --yes

# Make a copy of the source tree since we do destructive operations on it
rsync --exclude=build --exclude=.git --exclude=__pycache__ --exclude=node_modules --exclude=target \
    --exclude=htmlcov --exclude=app/coverage --exclude=app/dist --exclude=app/out \
    -av --no-times /src/ /srv/securedrop-client
cd /srv/securedrop-client

# HACK: Force installation of nodejs 24.15.0 to work around <https://github.com/electron/electron/issues/51619>.
cat >/etc/apt/preferences.d/nodejs <<'EOF'
Package: nodejs
Pin: version 24.15.0-1nodesource1
Pin-Priority: 1001
EOF

apt-get build-dep . --yes

# Tweak the changelog just a bit
./scripts/fixup-changelog.sh

dpkg-buildpackage --no-sign
ls ../
# Copy the built artifacts back and print checksums
mv -v ../*.{buildinfo,changes,deb,dsc,tar.gz} /build/
cd /build/
sha256sum ./*
