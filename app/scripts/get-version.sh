#!/usr/bin/env bash 

set -eo pipefail 
umask 077

# Get the version from package.json
echo $(cat "package.json" | grep '"version"' | cut -d'"' -f4)
