ARG DISTRO=bookworm
FROM debian:$DISTRO

RUN apt-get update && apt-get upgrade --yes && apt-get install -y ca-certificates
# FIXME: Do this to fool piuparts into thinking we didn't remove /opt during
# the package purge. Why does purging our packages not work properly?
RUN rm -rf /opt
# CI manifest will copy keyring into the build directory
COPY securedrop-keyring.gpg /usr/share/keyrings
