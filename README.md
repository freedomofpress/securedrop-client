# securedrop-client
[![CircleCI](https://circleci.com/gh/freedomofpress/securedrop-client.svg?style=svg)](https://circleci.com/gh/freedomofpress/securedrop-client)

Qt-based client for working with SecureDrop submissions on the SecureDrop Qubes Workstation. In Qubes, this application runs within a VM that has no direct network access, and files open in individual, non-networked, disposable VMs. API requests and responses to and from the SecureDrop application server are sent through an intermediate VM using the [Qubes SecureDrop proxy](https://github.com/freedomofpress/securedrop-proxy). For additional background, see the [main SecureDrop Workstation repository](https://github.com/freedomofpress/securedrop-workstation), and read about the [user research and design work that informs this work](https://github.com/freedomofpress/securedrop-ux/wiki/Qubes-Journalist-Workstation).

**IMPORTANT:** This project is in alpha and should not be used in production environments. There are known bugs which can be found in this project’s issue tracker.

# Current limitations

This client is under active development and currently supports a minimal feature set. Major supported features include:

- the download and decryption of files, messages, and replies (using [Qubes split-gpg](https://www.qubes-os.org/doc/split-gpg/))
- the display of decrypted messages and replies in a new conversation view
- the opening of all files in individual, non-networked, Qubes disposable VMs
- replying to sources
- deleting sources
- exporting files to LUKS-encrypted USB drives
- printing to supported printers

## Getting Started

Set up a Python 3 virtual environment and set up dependencies:

```
virtualenv --python=python3.7 .venv
source .venv/bin/activate
pip install --require-hashes -r dev-requirements.txt
```

Please install system libraries for PyQt rather than using PyPI-managed libraries- this makes packaging possible later. On Debian, `apt install python3-pyqt5 python3-pyqt5.qtsvg` will install what you need.

In order to run the test suite you should also install the `xvfb` package (to
make the `xvfb-run` command available): `apt install xvfb`. You may also need
to install the `sqlite3` command: `apt install sqlite3`.

### OSX

```
# install Homebrew https://brew.sh/

brew install pyenv
# follow step 3 onwards of https://github.com/pyenv/pyenv#basic-github-checkout
# install and select the latest version of python 3.7.x
pyenv install 3.7
pyenv local 3.7.x

brew install pip
pip install virtualenv
virtualenv --python=python3.7 .venv
source .venv/bin/activate
pip install --require-hashes -r dev-requirements.txt
```

## Updating dependencies

We have several dependency files: `dev-requirements.txt` and `requirements.txt` point to python software foundation hashes, and `build-requirements.txt` points to our builds of the wheels from our own pip mirror. Whenever a dependency in `build-requirements.txt` changes, our team needs to manually review the code in the dependency diff with a focus on spotting vulnerabilities.

If you're adding or updating a dependency, you need to:

1. Modify either `requirements.in` or `dev-requirements.in` (depending on whether it is prod or dev only) and then run `make update-pip-requirements`. This will generate `dev-requirements.txt` and `requirements.txt`.

2. For building a debian package from this project, we use the requirements in
`build-requirements.txt` which uses our pip mirror, i.e. the hashes in that file point to
wheels on our pip mirror. A maintainer will need to add
the updated dependency to our pip mirror (you can request this in the PR).

3. Once the pip mirror is updated, you should checkout the [securedrop-debian-packaging repo](https://github.com/freedomofpress/securedrop-debian-packaging) and run `make requirements`. Commit the `build-requirements.txt` that results and add it to your PR.

## Run the client

You can then run the client with an ephemeral data directory:

```
./run.sh
```

If you want to persist data across restarts, you will need to run the client with:

```
./run.sh --sdc-home /path/to/my/dir/
```

## AppArmor support

An AppArmor profile is available for mandatory access control. When installing securedrop-client from a .deb package, the AppArmor profile will automatically be copied and enforced. Below are instructions to use the profile in non-production scenarios.

### Requirements

1. The entrypoint for the application must be through `/usr/bin/securedrop-client` with application code in `/opt/venvs/securedrop-client`.

2. The kernel must support AppArmor (running `sudo aa-status` will return zero if AppArmor is supported).

3. The `apparmor-utils` package is installed (`sudo apt install apparmor-utils` in Debian).

### Enabling AppArmor

1. Copy `files/usr.bin.securedrop-client` to `/etc/apparmor.d/`.

2. `sudo aa-enforce /etc/apparmor.d/usr.bin.securedrop-client/`.

3. `sudo aa-status` and observe securedrop-client profile is being enforced.

### Testing and updating the AppArmor profile

1. Update the profile in `/etc/apparmor.d/usr.bin.securedrop-client`.

2. `sudo aa-teardown`.

3. `sudo service apparmor restart`.

4. Once you've made all the changes necessary (e.g.: no apparmor errors in `/var/log/syslog`) you can copy `/etc/apparmor.d/usr.bin.securedrop-client` into `files/usr.bin.securedrop-client` in this repository and commit the changes.

## Debugging

To use `pdb`, add these lines:

```
from PyQt5.QtCore import pyqtRemoveInputHook; pyqtRemoveInputHook()
import pdb; pdb.set_trace()
```
Then you can use [`pdb` commands](https://docs.python.org/3/library/pdb.html#debugger-commands) as normal.

Logs can be found in the `{sdc-home}/logs`. If you are debugging a version of this application installed from a deb package in Qubes, you can debug issues by looking at the log file in `~/.securedrop_client/logs/client.log`. You can also add additional log lines in the running code in
`/opt/venvs/securedrop-client/lib/python3.7/site-packages/securedrop_client/`.

## Running against a test server

In order to login, or take other actions involving network access, you will need to use the SecureDrop server dev container.

Follow the instructions [in the SecureDrop documentation](https://docs.securedrop.org/en/latest/development/setup_development.html#quick-start) to set that up.

The client uses the [SecureDrop SDK](https://github.com/freedomofpress/securedrop-sdk) to interact with the [SecureDrop Journalist API](https://docs.securedrop.org/en/latest/development/journalist_api.html).
After you run the server container, the journalist interface API will be running on `127.0.0.1:8081` with a test journalist, admin, and test sources and replies.

To ensure that file decryption works, please import [this test private key](https://raw.githubusercontent.com/freedomofpress/securedrop/0a901362b84a5378fba80e9cd0ffe4542bdcd598/securedrop/tests/files/test_journalist_key.sec) into your GnuPG keyring. Submissions in the SecureDrop server dev environment can be decrypted with this test key.

## Run the tests and checks

To run everything, run:

```bash
make check
```

To individually run the unit tests, run `make test` to run the suite in parallel (fast), or run `make test-random` to run the tests in random order (slower, but this is what `make check` runs and what runs in CI).

## Environments

The quickest way to get started with running the client is to use the [developer environment](#developer-environment) that [runs against a test server running in a local docker container](#running-against-a-test-server). This differs from a staging or production environment where the client receives and sends requests over Tor. Things are a lot snappier in the developer environment and can sometimes lead to a much different user experience, which is why it is important to do end-to-end testing in Qubes using the [staging environment](#staging-environment), especially if you are modifying code paths involving how we handle server requests and responses.

For reproducing production bugs or running demos, we recommend using the [Production Environment](#production-envrionment) that will allow you to test a nightly build of the client.

We support running the [developer environment on a non-Qubes OS](#developer-environment-on-a-non-qubes-os) for developer convenience. If this is your preferred environment, keep in mind that you, or a PR reviewer, will need to run tests in Qubes if you modify code paths involving any of the following:

* cryptography
* opening of files in VMs
* network (via the RPC service) traffic
* fine tuning of the graphical user interface

### Developer environment

* Run by `run.sh` inside a virtual env in the `sd-dev` AppVM
* Requires `qvm-tags sd-dev add sd-client` to be run in `dom0` (substitute your dev VM for `sd-dev`)
* Works with SecureDrop running in a local docker container, see [SecureDrop docs](https://docs.securedrop.org/en/latest/development/setup_development.html) for setup instructions, including post-installation steps for allowing docker to be run as a non-root user, which is a requirement on Qubes
* Uses a temporary directory as its configuration directory, instead of ` ~/.securedrop_client`
* Uses a development gpg private key inside a gpg keychain stored in the temporary configuration directory
* Submissions will be opened in DispVMs
* Tor is not used

### Developer environment on a non-Qubes OS

* Run by `run.sh` inside a virtual env on a non-Qubes OS
* Works with SecureDrop running in a local docker container, see [SecureDrop docs](https://docs.securedrop.org/en/latest/development/setup_development.html) for setup instructions
* Uses a temporary directory as its configuration directory, instead of ` ~/.securedrop_client`
* Uses a development gpg private key inside a gpg keychain stored in the temporary configuration directory
* Does not support opening submissions
* Tor is not used

### Staging environment

* Run by directly invoking the client `python -m securedrop_client` on the `sd-app` AppVM
* Requires that `make all` in the `securedrop-workstation` repository has completed successfully
* Requires that the installed client (e.g., nightly build) has been run at least once, or that
  the database has been [manually initialized](https://github.com/freedomofpress/securedrop-client/blob/master/files/securedrop-client)
* Uses `~/.securedrop_client` as its configuration directory
* Uses the gpg key in the `sd-gpg` AppVM configured during `make all`
* Tor is used: Requests/responses proxied via the `securedrop-proxy` RPC service
* For convienient access to network in order to clone the repository and push branches, you'll need to add a NetVM (`sys-firewall`)

### Production environment

* Run by executing `securedrop-client` in the `sd-app` AppVM (see [workstation documentation here](https://github.com/freedomofpress/securedrop-workstation/#using-the-securedrop-client))
* Requires that `make all` in the `securedrop-workstation` repository has completed successfully
* Uses `~/.securedrop_client` as its configuration directory
* Uses the gpg key in the `sd-gpg` AppVM configured during `make all`
* Tor is used: Requests/responses proxied via the `securedrop-proxy` RPC service

## Generate and run database migrations

```bash
rm -f svs.sqlite
sqlite3 svs.sqlite .databases > /dev/null
alembic upgrade head
alembic revision --autogenerate -m "describe your revision here"
```

### Merging Migrations

This project aims to have at most one migration per release. There may be cases where this is not feasible,
but developers should merge their migration into the latest migration that has been generated since the last
release. The above mentioned autogenerate command will not do this for you.

## Making a Release

**Note:** These are the release guidelines for pre-production alpha releases. Production release tags must
be signed with the SecureDrop release key.

1. Update versions: `./update_version.sh $new_version_number` and add a new entry in the changelog.
2. Commit the changes with commit message `securedrop-client $new_version_number` and make a PR.
3. You should confirm via a manual debian package build and manual testing in Qubes that there are no regressions (this is limited pre-release QA).
4. Once your PR is approved, you can add a tag and push: `git tag $new_version_number`.
