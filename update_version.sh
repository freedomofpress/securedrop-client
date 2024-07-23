#!/bin/bash
set -euxo pipefail

NEW_VERSION=${1:-""}

if [ -z "$NEW_VERSION" ]; then
  echo "Usage: ./update_version.sh <version>";
  exit 1
fi


if [[ $NEW_VERSION == *~rc* ]]; then
    echo "RCs should use the versioning a.b.c-rcD, where a.b.c is the next version"
    exit 1
fi

sed -i'' -r -e "s/^__version__ = \"(.*?)\"/__version__ = \"${NEW_VERSION}\"/" client/securedrop_client/__init__.py
sed -i'' -r -e "s/^__version__ = \"(.*?)\"/__version__ = \"${NEW_VERSION}\"/" export/securedrop_export/__init__.py

# Normalize version, convert any - to ~, e.g. 0.9.0-rc1 to 0.9.0~rc1
DEB_VERSION=$(echo "$NEW_VERSION" | sed 's/-/~/g')

export DEBEMAIL="securedrop@freedom.press"
export DEBFULLNAME="SecureDrop Team"
dch -b --newversion "${DEB_VERSION}" --distribution unstable "see changelog.md"
