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

GPG_HOME="$SDC_HOME/gpg"
mkdir -p "$GPG_HOME"
chmod 0700 "$SDC_HOME" "$GPG_HOME"

function cleanup {
  PID=$(ps -ef | grep gpg-agent | grep "$GPG_HOME" | grep -v grep | awk '{print $2}')
  if [ "$PID" ]; then
    kill "$PID"
  fi
}
trap cleanup EXIT

echo "Running app with home directory: $SDC_HOME"
echo ""

gpg --homedir "$GPG_HOME" --allow-secret-key-import --import tests/files/securedrop.gpg.asc &

# create the database and config for local testing
./create_dev_data.py "$SDC_HOME" &

# check whether current env is qubes
is_qubes="$(printenv | grep ^QUBES_)" || true

if [[ -n "$is_qubes" ]]; then
    echo "Detected QubesOS, enabling DispVMs for submission handling..."
    qubes_flag=""

    # Ensure we have mime handlers for open-in-dvm
    local_apps_dir="$HOME/.local/share/applications"
    mkdir -p "$local_apps_dir"
    cp files/open-in-dvm.desktop "$local_apps_dir"

    # Ensure desktop files are read from local dir
    export XDG_CONFIG_HOME="$PWD/files"
else
    echo "Current OS is *not* Qubes, disabling DispVM support..."
    qubes_flag="--no-qubes"
fi

wait

exec python -m securedrop_client --sdc-home "$SDC_HOME" --no-proxy "$qubes_flag" $@
