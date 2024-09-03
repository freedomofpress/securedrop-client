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

PYTHON="poetry run python"
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

# Import the test key for decryption of submissions and encryption of replies...
gpg --allow-secret-key-import --import tests/files/securedrop.gpg.asc
# ...and specify what key should be used to encrypt replies.
export SD_SUBMISSION_KEY_FPR="65A1B5FF195B56353CC63DFFCC40EF1228271441"

echo "Building proxy..."
make -C ../proxy build

# create the database and config for local testing
poetry run python create_dev_data.py "$SDC_HOME" &

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

echo "Starting client, home directory: $SDC_HOME"
# Create the log file ahead of time so we can tail it before the client launches
mkdir -p "$SDC_HOME/logs"
touch "$SDC_HOME/logs/client.log"
tail -f "$SDC_HOME/logs/client.log" &
LOGLEVEL=debug $PYTHON -m securedrop_client --sdc-home "$SDC_HOME" --no-proxy "$qubes_flag" "$@"
