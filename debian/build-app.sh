#!/bin/bash

set -euxo pipefail

# Install pnpm v10
npm install -g pnpm@10

cd app

pnpm install --frozen-lockfile
pnpm run build:unpack
