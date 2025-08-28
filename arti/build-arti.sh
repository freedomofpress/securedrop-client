#!/bin/bash

set -euxo pipefail

gpg --import upstream-keys/*.asc

TAG="arti-v$1"

echo "Building $TAG"
git clone https://gitlab.torproject.org/tpo/core/arti --depth 1 -b "$TAG" arti-upstream
cd arti-upstream
git --no-pager log -1 --oneline --show-signature --no-color
git --no-pager tag -v "$TAG"

CARGO_PROFILE_RELEASE_DEBUG=full cargo build --release --locked --bin arti
