#!/bin/bash
# shellcheck disable=SC2086
set -euxo pipefail

NAME=$1
PIP_ARGS="--ignore-installed --no-binary=:all: --no-deps --no-cache-dir --no-build-isolation"

/usr/bin/python3 -m venv --system-site-packages ./debian/securedrop-${NAME}/opt/venvs/securedrop-${NAME}
if [[ -f "${NAME}/build-requirements.txt" ]]; then
    ./debian/securedrop-${NAME}/opt/venvs/securedrop-${NAME}/bin/pip install $PIP_ARGS --require-hashes \
        -r ${NAME}/build-requirements.txt
fi
./debian/securedrop-${NAME}/opt/venvs/securedrop-${NAME}/bin/pip install --no-index $PIP_ARGS ./${NAME}

# Adjust paths to reflect installed paths
find ./debian/securedrop-${NAME}/ -type f -exec sed -i "s#$(pwd)/debian/securedrop-${NAME}##" {} \;
# Cleanup wheels
rm -rf ./debian/securedrop-${NAME}/opt/venvs/securedrop-${NAME}/share/python-wheels
