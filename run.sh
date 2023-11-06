#!/usr/bin/env bash

set -eo pipefail
umask 077

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

source scripts/setup-tmp-directories.sh

PYTHON="python"
if [[ $OSTYPE == 'darwin'* ]] && [[ "$(uname -m)" == "arm64" ]]; then
    PYTHON="arch -x86_64 ${PYTHON}"
fi

GNUPGHOME="$SDC_HOME/gpg"
export GNUPGHOME
mkdir -p "$GNUPGHOME"
chmod 0700 "$SDC_HOME" "$GNUPGHOME"

function cleanup {
    gpgconf --kill gpg-agent
}
trap cleanup EXIT

echo "Running app with home directory: $SDC_HOME"
echo ""

cleanup

gpg --allow-secret-key-import --import tests/files/securedrop.gpg.asc &

# create the database and config for local testing
./create_dev_data.py "$SDC_HOME" &

# check whether current env is qubes
is_qubes="$(printenv | grep ^QUBES_)" || true

if [[ -n "$is_qubes" ]]; then
    echo "Detected QubesOS, enabling DispVMs for submission handling..."
    qubes_flag=""

    # Ensure desktop files are read from local dir
    export XDG_CONFIG_HOME="$PWD/files"
else
    echo "Current OS is *not* Qubes, disabling DispVM support..."
    qubes_flag="--no-qubes"
fi

if [[ $XDG_SESSION_TYPE = "wayland" ]]; then
    echo "Detected Wayland, will run with QT_QPA_PLATFORM variable..."
    export QT_QPA_PLATFORM=wayland
fi

wait

echo "Starting client, log available at: $SDC_HOME/logs/client.log"
$PYTHON -m securedrop_client --sdc-home "$SDC_HOME" --no-proxy "$qubes_flag" "$@"
