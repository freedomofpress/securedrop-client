ARG DISTRO=bookworm
FROM debian:$DISTRO

RUN apt-get update && apt-get upgrade --yes && apt-get install -y ca-certificates curl
# FIXME: Do this to fool piuparts into thinking we didn't remove /opt during
# the package purge. Why does purging our packages not work properly?
RUN rm -rf /opt
# TODO: can we avoid this? we don't have an easily extractable pubkey file anymore
RUN curl https://keys.openpgp.org/vks/v1/by-fingerprint/2359E6538C0613E652955E6C188EDD3B7B22E6A3 \
    > /usr/share/keyrings/securedrop-keyring.asc
