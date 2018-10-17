#!/usr/bin/env bash
set -e

HOME=$(mktemp -d)

echo "Running app with home directory: $HOME"

exec python -m securedrop_client --home "$HOME"
