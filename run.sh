#!/usr/bin/env bash
set -e

while [ -n "$1" ]; do
  param="$1"
  value="$2"
  case $param in
    --sdc-home)
        SDC_HOME="$value"
        shift
        ;;
    *)
    break
  esac
  shift
done

SDC_HOME=${SDC_HOME:-$(mktemp -d)}

echo "Running app with home directory: $SDC_HOME"

# create the database for local testing

python - << EOF
from securedrop_client.models import Base, make_engine
Base.metadata.create_all(make_engine("$SDC_HOME"))
EOF

exec python -m securedrop_client --sdc-home "$SDC_HOME" $@
