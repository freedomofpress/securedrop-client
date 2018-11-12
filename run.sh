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

export SDC_HOME

chmod 0700 $SDC_HOME

echo "Running app with home directory: $SDC_HOME"

# create gpg directory, add private key
mkdir -p "${SDC_HOME}/gpg"
chmod 0700 "${SDC_HOME}/gpg"
gpg --homedir "${SDC_HOME}/gpg" --trust-model always --import files/dev_key.asc

# create the database for local testing
./createdb.py $SDC_HOME

exec python -m securedrop_client --sdc-home "$SDC_HOME" --no-proxy $@
