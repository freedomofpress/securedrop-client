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

# We're going to store artifacts in a temp directory
BUILD_DEST=$(mktemp -d)

$OCI_BIN run --rm $OCI_RUN_ARGUMENTS \
    -v "${BUILDER}:/builder:Z" \
    -v "${BUILD_DEST}:/build:Z" \
    --env NIGHTLY="${NIGHTLY:-}" \
    --entrypoint "/src/scripts/build-debs-real.sh" \
    $CONTAINER

ls "$BUILD_DEST"
# Copy the build artifacts to our project's /build
mkdir -p build
cp ${BUILD_DEST}/* build/

FAST="${FAST:-}"
if [[ -z $FAST ]]; then
    CONTAINER2="fpf.local/sd-client-lintian"
    $OCI_BIN build scripts/lintian -t $CONTAINER2
    # Display verbose info, and fail on warnings and errors.
    $OCI_BIN run --rm $OCI_RUN_ARGUMENTS -v "${BUILD_DEST}:/build:Z" $CONTAINER2 \
        bash -c \
            "lintian --version && lintian \
            --info --tag-display-limit 0 \
            --fail-on warning --fail-on error \
            /build/*.changes \
            && echo OK"
fi

# Clean up temp stuff now that lintian is done (or skipped)
rm -rf "${BUILD_DEST}"
echo "Build completed successfully. Artifacts and their checksums are:"
sha256sum build/*.deb
