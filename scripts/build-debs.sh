#!/bin/bash
# shellcheck disable=SC2209,SC2086
# Build packages! This script is configured by environment variables:
# `BUILDER`: relative path to the securedrop-builder repository,
#            defaults to "../securedrop-builder"
# `DEBIAN_VERSION`: codename to build for, defaults to "bullseye"
# `NIGHTLY`: if set, add current time to the version number

# This script runs *outside* the container.

set -euxo pipefail

git --no-pager log -1 --oneline --show-signature --no-color

OCI_RUN_ARGUMENTS="--user=root -v $(pwd):/src:Z"

# Default to podman if available
if which podman > /dev/null 2>&1; then
    OCI_BIN="podman"
    # Make sure host UID/GID are mapped into container,
    # see podman-run(1) manual.
    OCI_RUN_ARGUMENTS="${OCI_RUN_ARGUMENTS} --userns=keep-id"
else
    OCI_BIN="docker"
fi
# Pass -it if we're a tty
if test -t 0; then
    OCI_RUN_ARGUMENTS="${OCI_RUN_ARGUMENTS} -it"
fi

# Look for the builder repo with our local wheels
BUILDER=$(realpath "${BUILDER:-../securedrop-builder}")
if [[ ! -d $BUILDER ]]; then
    echo "Cannot find securedrop-builder repository, please check it out \
to ${BUILDER} or set the BUILDER variable"
    exit 1
fi

export BUILDER
export DEBIAN_VERSION="${DEBIAN_VERSION:-bullseye}"
export OCI_RUN_ARGUMENTS
export OCI_BIN
export CONTAINER="fpf.local/sd-client-builder-${DEBIAN_VERSION}"

. ./scripts/image_prep.sh

$OCI_BIN run --rm $OCI_RUN_ARGUMENTS \
    -v "${BUILDER}:/builder:Z" \
    --env NIGHTLY="${NIGHTLY:-}" \
    --entrypoint "/src/scripts/build-debs-real.sh" \
    $CONTAINER
