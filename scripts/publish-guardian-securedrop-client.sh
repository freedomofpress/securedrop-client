#!/bin/bash
# This script is designed to be run on a debain build server. It handles the process of signing a .deb package and publishing
# it to the guardian's APT repository in amazon S3. Where the signing key is encrypted there will be a prompt for the password
set -e

VERSION=$1
DEB_LOCATION=$2
STAGE=$3

SCRIPT_PATH=$( cd $(dirname $0) ; pwd -P )

print_usage_and_exit () {
  cat << EOF
Usage: publish-securedrop.sh VERSION DEB_LOCATION STAGE

e.g. ./publish-securedrop.sh 100.8.1 securedrop.deb CODE
EOF
  exit 1
}

if [ -z "$VERSION" ]; then
    echo "Version must be provided"
    print_usage_and_exit
    exit 1
fi

if [ -z "$DEB_LOCATION" ]; then
    echo "Fully qualified location of the deb file you want to publish should be provided"
    print_usage_and_exit
    exit 1
fi

# check if signing key secret id code or prod

if [ "$STAGE" == "CODE" ] ||  [ "$STAGE" == "PROD" ]; then
  SECRET_NAME="securedrop-workstation-repository-private-$STAGE"
  SIGNING_KEY_SECRET_ID=$(aws secretsmanager list-secrets --filter Key=name,Values=$SECRET_NAME  --region eu-west-1 --query "SecretList[?Name=='$SECRET_NAME'].ARN" --output text)
else
  echo "STAGE must be provided as CODE or PROD"
  exit 1
fi

LOWER_STAGE=$(echo $STAGE | tr '[:upper:]' '[:lower:]')

echo "Updating aptly config"
S3_ENDPOINTS=$(aws ssm get-parameter --name /investigations/aptly-s3-publish-endpoints --region eu-west-1 | jq -r .Parameter.Value)
echo "Updating aptly config file $HOME/.aptly.conf"
aptly config show | jq ".architectures = [\"amd64\"] | .S3PublishEndpoints = ${S3_ENDPOINTS}" > /tmp/aptly.conf
cat /tmp/aptly.conf
mv /tmp/aptly.conf $HOME/.aptly.conf

REPO_NAME="gu-securedrop"
SNAPSHOT_NAME="$REPO_NAME-$VERSION"
KEYRING="temp-keyring.gpg"
# Aptly is possibly a bit more full featured than we need - it allows a local version of a repository
# Rather than keep this in sync between different developer machines, here we drop everything local before publishing

# Note - aptly needs a configuration file in order to e.g. know which s3 bucket to publish to. This should be preloaded
# onto the server automatically in /home/ubuntu/.aptly.conf

# Remove any local aptly stuff - || true is there because we don't want this script to fail if there's not existing stuff
aptly repo drop -force "$REPO_NAME" || true
aptly publish drop bookworm s3:guardian-securedrop-repo-$LOWER_STAGE: || true
aptly snapshot drop "$SNAPSHOT_NAME" || true

# Fetch signing key
aws secretsmanager get-secret-value --region eu-west-1 --secret-id "$SIGNING_KEY_SECRET_ID" | jq .SecretString -r > /tmp/private.asc

# Import key into temporary keyring
gpg2 --no-default-keyring --pinentry loopback --keyring "$KEYRING" --import /tmp/private.asc

rm /tmp/private.asc

# Publish debs to S3
aptly repo create -distribution=bookworm -component=main "$REPO_NAME"
aptly repo add "$REPO_NAME" "$DEB_LOCATION"
aptly snapshot create "$SNAPSHOT_NAME" from repo "$REPO_NAME"

aptly publish snapshot -keyring="$KEYRING" "$SNAPSHOT_NAME" s3:guardian-securedrop-repo-$LOWER_STAGE:

# Remove temporary keyring
rm ~/.gnupg/$KEYRING
