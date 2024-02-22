#!/bin/bash

cd /home/user/projects/securedrop-proxy
virtualenv .venv
source .venv/bin/activate
pip install --require-hashes -r requirements.txt
pip install --require-hashes -r dev-requirements.txt
./sd-proxy.py ./config.yaml
