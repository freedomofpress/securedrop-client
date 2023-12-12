#!/bin/bash
set -euxo pipefail

NAME=$1
if [[ $NAME == "client" ]]; then
    VENV_ARGS="--system-site-packages"
else
    VENV_ARGS=""
fi
WHEELS_DIR="/builder/securedrop-${NAME}/wheels"
PIP_ARGS="--ignore-installed --no-index --find-links ${WHEELS_DIR} --no-deps --no-cache-dir --no-use-pep517"

/usr/bin/python3 -m virtualenv $VENV_ARGS ./debian/securedrop-${NAME}/opt/venvs/securedrop-${NAME}
./debian/securedrop-${NAME}/opt/venvs/securedrop-${NAME}/bin/pip install $PIP_ARGS -r ${NAME}/build-requirements.txt
./debian/securedrop-${NAME}/opt/venvs/securedrop-${NAME}/bin/pip install $PIP_ARGS ./${NAME}

# Adjust paths to reflect installed paths
find ./debian/securedrop-${NAME}/ -type f -exec sed -i "s#$(pwd)/debian/securedrop-${NAME}##" {} \;
# Cleanup wheels
rm -rf ./debian/securedrop-${NAME}/opt/venvs/securedrop-${NAME}/share/python-wheels
