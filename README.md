# securedrop-client
[![CircleCI](https://circleci.com/gh/freedomofpress/securedrop-client.svg?style=svg)](https://circleci.com/gh/freedomofpress/securedrop-client)

Qt-based client for working with SecureDrop submissions on the SecureDrop Qubes Workstation. For additional background, see the [main SecureDrop Workstation repository](https://github.com/freedomofpress/securedrop-workstation), and read about the [user research and design work that informs this work](https://github.com/freedomofpress/securedrop-ux/wiki/Qubes-Journalist-Workstation).

## Getting Started

Set up a Python 3 virtual environment and set up dependencies:

```
pipenv install --dev
pipenv shell
```

Please install system libraries for PyQt rather than using PyPI-managed libraries- this makes packaging possible later. On Debian, `apt install python3-pyqt5 python3-pyqt5.qtsvg` will install what you need.

In order to run the test suite you should also install the `xvfb` package (to
make the `xvfb-run` command available): `apt install xvfb`.

### OSX

```
# install Homebrew https://brew.sh/

brew install pyenv
# follow step 3 onwards of https://github.com/pyenv/pyenv#basic-github-checkout
pyenv install 3.5.0

brew install pip
pip install pipenv
pipenv install --dev
pipenv shell
```

## Run the client

To ensure that file decryption works, please import [this test private key](https://raw.githubusercontent.com/freedomofpress/securedrop/0a901362b84a5378fba80e9cd0ffe4542bdcd598/securedrop/tests/files/test_journalist_key.sec) into your GnuPG keyring. Submissions in the SecureDrop development environment can be decrypted with this test key.

You can then run the client with an ephemeral data directory:

```
./run.sh
```

If you want to persist data across restarts, you will need to run the client with:

```
./run.sh --sdc-home /path/to/my/dir/
```

## Run tests

```
make test
```

## Generate and run database migrations

```
alembic revision --autogenerate -m "describe your revision here"
alembic upgrade head
```

## Qubes Integration

This client will sit in a Qubes vault AppVM:

[![diagram](https://user-images.githubusercontent.com/7832803/39219841-d7037bb4-47e1-11e8-84dc-eaaaa06ef87b.png)](https://github.com/freedomofpress/securedrop-workstation/issues/88)

It will use the [SecureDrop SDK](https://github.com/freedomofpress/securedrop-sdk)
to interact with the [SecureDrop Journalist API](https://docs.securedrop.org/en/latest/development/journalist_api.html).
Currently, this must be done by running the SecureDrop server dev container. To do this:

1. Follow the instructions [in the SecureDrop documentation](https://docs.securedrop.org/en/latest/development/setup_development.html#quick-start) to set up the development container. The journalist interface API will be running on `127.0.0.1:8081` with a test
journalist, admin, and test sources and replies.
2. Clone the [SDK repository]((https://github.com/freedomofpress/securedrop-sdk) and install the package (`pip install ../path/to/securedrop-sdk`) in the same virtualenv you are using to develop this client.
3. Now at the Python interpreter you should be able to `import sdclientapi` without issue.

For further development, you should use the SDK methods to interact with the server.
