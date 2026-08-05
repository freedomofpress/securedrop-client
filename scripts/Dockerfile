ARG DISTRO=trixie
FROM debian:$DISTRO

# ARGs must be repeated for every different build stage
ARG DISTRO

ENV PIP_DISABLE_PIP_VERSION_CHECK=1
ENV PIP_PROGRESS_BAR=off
ENV CARGO_TERM_COLOR=never
ENV CARGO_TERM_PROGRESS_WHEN=never

RUN apt-get update && apt-get --yes upgrade && apt-get install --yes build-essential curl rsync rustup

COPY scripts/qubes_43.sources /etc/apt/sources.list.d/
RUN sed -i s/##VERSION_CODENAME##/${DISTRO}/ /etc/apt/sources.list.d/qubes_43.sources
COPY scripts/nodesource-node24.sources /etc/apt/sources.list.d/

COPY rust-toolchain.toml /rust-toolchain.toml
ENV CARGO_HOME /opt/cargo
# This is sufficient to get it to download the correct Rust toolchain
RUN rustup show
