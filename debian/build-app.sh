#!/bin/bash

set -euxo pipefail

COREPACK_HOME="$(mktemp -d)"
COREPACK_SHIMS="$(mktemp -d)"
export COREPACK_HOME
export PATH="$COREPACK_SHIMS:$PATH"
cleanup_corepack_home() {
    rm -R "$COREPACK_HOME" "$COREPACK_SHIMS"
}
trap cleanup_corepack_home EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

cd app

corepack enable --install-directory "$COREPACK_SHIMS"
corepack install

pnpm install --frozen-lockfile
pnpm run build:unpack
