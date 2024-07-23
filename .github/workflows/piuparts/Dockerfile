ARG DISTRO=bookworm
FROM debian:$DISTRO

# ARGs must be repeated for every different build stage
ARG DISTRO
RUN apt-get update && apt-get upgrade --yes && apt-get install -y ca-certificates \
    curl dpkg-dev
# FIXME: Do this to fool piuparts into thinking we didn't remove /opt during
# the package purge. Why does purging our packages not work properly?
RUN rm -rf /opt

# Set up a local package repository
RUN mkdir -p /packages
COPY packages/*.deb /packages/
WORKDIR /packages
RUN dpkg-scanpackages . > /packages/Packages
WORKDIR /
RUN echo "deb [trusted=yes] file:/packages ./" > /etc/apt/sources.list.d/local.list

# Note: we use a different filename as the package so removing the package doesn't
# remove this version and cause piuparts to fail.
COPY apt_freedom_press.sources /etc/apt/sources.list.d/piuparts-apt_freedom_press.sources
RUN sed -i s/##VERSION_CODENAME##/bookworm/ /etc/apt/sources.list.d/piuparts-apt_freedom_press.sources
COPY qubes_42.sources /etc/apt/sources.list.d/
RUN sed -i s/##VERSION_CODENAME##/${DISTRO}/ /etc/apt/sources.list.d/qubes_42.sources
