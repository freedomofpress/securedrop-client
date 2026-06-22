#!/bin/bash
# shellcheck disable=SC2086
set -euxo pipefail

NAME=$1
WHEELS_DIR="/builder/securedrop-${NAME}/wheels"
PIP_ARGS="--ignore-installed --no-index --find-links ${WHEELS_DIR} --no-deps --no-cache-dir --no-build-isolation"

/usr/bin/python3 -m venv --system-site-packages ./debian/securedrop-${NAME}/opt/venvs/securedrop-${NAME}
./debian/securedrop-${NAME}/opt/venvs/securedrop-${NAME}/bin/pip install $PIP_ARGS --require-hashes \
    -r ${NAME}/build-requirements.txt
./debian/securedrop-${NAME}/opt/venvs/securedrop-${NAME}/bin/pip install $PIP_ARGS ./${NAME}

# Adjust paths to reflect installed paths
find ./debian/securedrop-${NAME}/ -type f -exec sed -i "s#$(pwd)/debian/securedrop-${NAME}##" {} \;
# Cleanup wheels
rm -rf ./debian/securedrop-${NAME}/opt/venvs/securedrop-${NAME}/share/python-wheels
