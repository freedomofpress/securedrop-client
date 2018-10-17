#!/usr/bin/env bash
set -e

HOME=$(mktemp -d)

echo "Running app with home directory: $HOME"

# create the database for local testing

python - << EOF
from securedrop_client.models import Base, make_engine
Base.metadata.create_all(make_engine("$HOME"))
EOF

exec python -m securedrop_client --home "$HOME"
