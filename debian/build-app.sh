#!/bin/bash

set -euxo pipefail

cd app

corepack enable
corepack install

pnpm install --frozen-lockfile
pnpm run build:unpack
