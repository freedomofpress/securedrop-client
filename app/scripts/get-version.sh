#!/usr/bin/env bash 

set -eo pipefail 
umask 077

# Get the version from package.json
grep '"version"' package.json | cut -d'"' -f4
