ARG DISTRO=bookworm
FROM debian:$DISTRO

# ARGs must be repeated for every different build stage
ARG DISTRO

ENV PIP_DISABLE_PIP_VERSION_CHECK=1
ENV PIP_PROGRESS_BAR=off
ENV CARGO_TERM_COLOR=never
ENV CARGO_TERM_PROGRESS_WHEN=never

RUN apt-get update && apt-get --yes upgrade && apt-get install --yes build-essential curl rsync

COPY qubes_42.sources /etc/apt/sources.list.d/
RUN sed -i s/##VERSION_CODENAME##/${DISTRO}/ /etc/apt/sources.list.d/qubes_42.sources
COPY nodesource-node22.sources /etc/apt/sources.list.d/

# Keep in sync with rust-toolchain.toml
ENV RUST_VERSION 1.90.0
ENV RUSTUP_VERSION 1.28.2
ENV RUSTUP_INIT_SHA256 20a06e644b0d9bd2fbdbfd52d42540bdde820ea7df86e92e533c073da0cdd43c
ENV RUSTUP_HOME /opt/rustup
ENV CARGO_HOME /opt/cargo

# Install Rust using the same steps as <https://github.com/rust-lang/docker-rust>
# 1) Download rustup-init and verify it matches hardcoded checksum
# 2) Run it to install rustup and the rustc/cargo "minimal" toolchain
# 3) Add `/opt/cargo/bin` to $PATH, which is where cargo & rustc are installed
RUN TMPDIR=`mktemp -d` && cd ${TMPDIR} \
        && curl --proto '=https' --tlsv1.2 -OO -sSf https://static.rust-lang.org/rustup/archive/${RUSTUP_VERSION}/x86_64-unknown-linux-gnu/rustup-init \
        && echo "${RUSTUP_INIT_SHA256} *rustup-init" | sha256sum -c - \
        && chmod +x rustup-init \
        && ./rustup-init --default-toolchain=${RUST_VERSION} --profile minimal -y \
        && cd && rm -rf ${TMPDIR}
ENV PATH "$PATH:/opt/cargo/bin/"
