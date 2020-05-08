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

The quickest way to get started with running the client is to use the [developer environment](#developer-environment) that [runs against a test server running in a local docker container](#running-against-a-test-server). This differs from a staging or production environment where the client receives and sends requests over Tor. Things are a lot snappier in the developer environment and can sometimes lead to a much different user experience, which is why it is important to do end-to-end testing in Qubes using the [staging environment](#staging-environment), especially if you are modifying code paths involving how we handle server requests and responses.

For reproducing production bugs or running demos, we recommend using the [Production Environment](#production-envrionment) that will allow you to test a nightly build of the client.

We support running the [developer environment on a non-Qubes OS](#developer-environment-on-a-non-qubes-os) for developer convenience. If this is your preferred environment, keep in mind that you, or a PR reviewer, will need to run tests in Qubes if you modify code paths involving any of the following:

* cryptography
* opening of files in VMs
* network (via the RPC service) traffic
* fine tuning of the graphical user interface

### Running against a test server

In order to login, or take other actions involving network access, you will need to run the client against a SecureDrop server. If you don't have a production server or want to test against a test server, you can install a SecureDrop server inside a dev container by following the instructions [in the SecureDrop documentation](https://docs.securedrop.org/en/latest/development/setup_development.html#quick-start).

The client uses the [SecureDrop SDK](https://github.com/freedomofpress/securedrop-sdk) to interact with the [SecureDrop Journalist API](https://docs.securedrop.org/en/latest/development/journalist_api.html). After you run the server container, the journalist interface API will be running on `127.0.0.1:8081` with a test journalist, admin, and test sources and replies.

To ensure that file decryption works, please import [this test private key](https://raw.githubusercontent.com/freedomofpress/securedrop/0a901362b84a5378fba80e9cd0ffe4542bdcd598/securedrop/tests/files/test_journalist_key.sec) into your GnuPG keyring. Submissions in the SecureDrop server dev environment can be decrypted with this test key.

### Developer environment

Running the client in a developer environment will use a temporary directory as its configuration directory, instead of ` ~/.securedrop_client`. A development gpg private key inside a gpg keychain is stored in the temporary configuration directory, which will be used to decrypt messages sent from the server running in the local docker container.

The SecureDrop client will open or export file submissions within disposable AppVms.

Tor is not used in the developer environment. If you want to use a Tor connection between the client and server, then you'll need to follow the [staging environment](#staging-environment) instructions instead.

1. Open a terminal in the `sd-app` AppVM in Qubes

2. Run a SecureDrop server in a local docker container

See [SecureDrop docs](https://docs.securedrop.org/en/latest/development/setup_development.html) for setup instructions, including post-installation steps for allowing docker to be run as a non-root user, which is a requirement on Qubes.

3. In a new terminal tab, clone the SecureDrop Client repo and set up its virtual environment

```
git clone git@github.com:freedomofpress/securedrop-client.git
cd securedrop-client
virtualenv --python=python3.7 .venv
source .venv/bin/activate
pip install --require-hashes -r requirements/dev-requirements.txt
```

4. Run SecureDrop Client

```
./run.sh
```

Or, if you want to persist data across restarts, you will need to run the client with:

```
./run.sh --sdc-home /path/to/my/configuration/directory
```

### Developer environment on a non-Qubes OS

Running the client in a developer environment will use a temporary directory as its configuration directory, instead of ` ~/.securedrop_client`. A development gpg private key inside a gpg keychain is stored in the temporary configuration directory, which will be used to decrypt messages.

If you want to be able to open or export file submissions in a disposable AppVM, then you'll need to follow the instructions for running this in a [developer environment](#developer-environment) in Qubes.

Tor is not used in the developer environment. If you want to use a Tor connection between the client and server, then you'll need to follow the [staging environment](#staging-environment) instructions instead.

1. Open a terminal from your non-Qubes OS

2. Run a SecureDrop server in a local docker container

See [SecureDrop docs](https://docs.securedrop.org/en/latest/development/setup_development.html) for setup instructions.

3. In a new terminal tab, clone the SecureDrop Client repo and set up its virtual environment

```
git clone git@github.com:freedomofpress/securedrop-client.git
cd securedrop-client
virtualenv --python=python3.7 .venv
source .venv/bin/activate
pip install --require-hashes -r requirements/dev-requirements.txt
```

4. Run SecureDrop Client

```
./run.sh
```

Or, if you want to persist data across restarts, you will need to run the client with:

```
./run.sh --sdc-home /path/to/my/configuration/directory
```

### Staging environment

Running the SecureDrop client in a staging environment will use a `~/.securedrop_client` as its configuration directory. The gpg key in the `sd-gpg` AppVM configured during `make all` will be used to decrypt messages.

The SecureDrop client will open or export file submissions within disposable AppVms.

Requests and responses between the client and server use a Tor connection, which are proxied via the `securedrop-proxy` AppVM's RPC service.


1. Run a SecureDrop staging server

See [SecureDrop docs on setting up a staging server](https://docs.securedrop.org/en/latest/development/virtual_environments.html#staging) or [SecureDrop docs on setting up a staging server in Qubes](https://docs.securedrop.org/en/latest/development/qubes_staging.html#deploying-securedrop-staging-instance-on-qubes)

2. Open a terminal in `dom0` in Qubes

3. Create a `config.json` file

```
cd securedrop-worksation
cp config.json.example config.json
vi config.json
```

`config.json.example` already contains the staging server's submission key fingerprint (and `sd-journalist.sec` already contains the staging server's private submission key) so all you need to do is update the hidserv hostname and key in `config.json`. To find this information, you can run `sudo cat /var/lib/tor/services/journalist/hostname` on you staging server.

4. Run `make all` to configure the AppVms

5. Open a terminal in the `sd-app` AppVM

6. Initialize the SecureDrop Client database by running the installed client (e.g. nightly build) once by running:

```
securedrop-client
```

Or [manually initialize](https://github.com/freedomofpress/securedrop-client/blob/HEAD/files/securedrop-client) the SecureDrop Client database.

8. To run a different version of the client, first add a NetVM (`sys-firewall`) to `sd-app` via its Qubes Settings so you can clone the client repository, and then follow these steps:

```
git clone git@github.com:freedomofpress/securedrop-client.git
cd securedrop-client
virtualenv --python=python3.7 .venv
source .venv/bin/activate
pip install --require-hashes -r requirements/dev-requirements.txt
```

9. Run the client

```
python -m securedrop_client
```

### Production environment

Running the SecureDrop client in a production environment will use a `~/.securedrop_client` as its configuration directory. The gpg key in the `sd-gpg` AppVM configured during `make all` will be used to decrypt messages.

The SecureDrop client will open or export file submissions within disposable AppVms.

Requests and responses between the client and server use a Tor connection, which are proxied via the `securedrop-proxy` AppVM's RPC service.

1. Run a SecureDrop server

See [SecureDrop docs on setting up a server](https://docs.securedrop.org/en/latest/install.html)

2. Open a terminal in `dom0` in Qubes

3. Create a `config.json` file

```
cd securedrop-worksation
cp config.json.example config.json
vi config.json
```

Update the hidserv hostname and key in `config.json`. To find this information, you can run `sudo cat /var/lib/tor/services/journalist/hostname` on you staging server. Update the Submission Key fingerprint as well.

4. Create an `sd-journalist.sec` file

Create `sd-journalist.sec` in the `securedrop-workstation` directory in `dom0` and copy your server's private submission key to this file. You can find this key in `~/Persistent/securedrop/install_files/ansible-base` on the Tails drive you used to set up your SecureDrop server.

5. Run the nightly build of the client by double-clicking the SecureDrop shortcut on your Qubes Desktop

```
securedrop-client
```

### OSX

```
# install Homebrew https://brew.sh/

brew install pyenv
# follow step 3 onwards of https://github.com/pyenv/pyenv#basic-github-checkout
# install and select the latest version of python 3.7.x
pyenv install 3.7.x
pyenv local 3.7.x

pip install virtualenv
virtualenv --python=python3.7 .venv
source .venv/bin/activate
pip install --require-hashes -r requirements/dev-mac-requirements.txt
```

## Updating dependencies

We have several dependency files: `dev-requirements.txt` (Linux), `dev-mac-requirements.txt` (macOS) and `requirements.txt` point to python software foundation hashes, and `build-requirements.txt` points to our builds of the wheels from our own pip mirror (https://pypi.securedrop.org/). Whenever a dependency in `build-requirements.txt` changes, our team needs to manually review the code in the dependency diff with a focus on spotting vulnerabilities.

If you're adding or updating a dependency, you need to:

1. Modify either `requirements.in` or `dev-requirements.in` (depending on whether it is prod or dev only) and then run `make update-pip-requirements`. This will generate `dev-requirements.txt` and `requirements.txt`.

2. For building a debian package from this project, we use the requirements in
`build-requirements.txt` which uses our pip mirror, i.e. the hashes in that file point to
wheels on our pip mirror. A maintainer will need to add
the updated dependency to our pip mirror (you can request this in the PR).

3. Once the pip mirror is updated, you should checkout the [securedrop-debian-packaging repo](https://github.com/freedomofpress/securedrop-debian-packaging) and run `make requirements`. Commit the `build-requirements.txt` that results and add it to your PR.


## Generating and running database migrations

```bash
rm -f svs.sqlite
sqlite3 svs.sqlite .databases > /dev/null
alembic upgrade head
alembic revision --autogenerate -m "describe your revision here"
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

## Running tests and checks

In order to run the test suite you should also install the `xvfb` package (to make the `xvfb-run` command available): `apt install xvfb`. You may also need to install the `sqlite3` command: `apt install sqlite3`.

To run all tests and checks, run:

```bash
make check
```

To only run unit tests, run:

```bash
make test
```

To run unit tests in random order, run:

```bash
make test-random
```

To only run integration tests, run:

```bash
make test-integration
```

To only run functional tests, run:

```bash
make test-functional
```

### Functional Tests

When functional tests are run, they replay recorded API request and response data instead of making actual API calls to a server. This is why tests can pass even when there is no server running. If you want to add new tests that make API calls or if the SDK ever changes its API, then you'll need to record new request and response data by following the steps outlined in [Generating new cassettes](#generating-new-cassettes).

We use `qtbot`, bundled with the [pytest-qt](https://pytest-qt.readthedocs.io/en/latest/) package, for UI interaction within our functional tests.

#### Generating new cassettes

We use [vcrpy](https://vcrpy.readthedocs.io/en/latest/) to record and replay API calls. Each request made from a test and response from the server is stored in a "cassette" yaml file in the `tests/functional/cassettes` directory.

If the SDK changes its API, then you'll see the following warning indicating that a request failed to be found in an existing cassette and that you'll need to regenerate cassettes:

```
Can't overwrite existing cassette ('<path-to-cassette-for-a-functional-test>') in your current record mode ('once').
```

To set up a local dev server and generate cassettes, follow these steps:

1. Bypass TOTP verification so that we can use the TOTP value of `123456` hard-coded in `tests/conftest.py`. You can do this by applying the following patch to the server code:

https://gist.github.com/creviera/8793d5ec4d28f034f2c1e8320a93866a

2. Start the server in a docker container by running:

    ```bash
    NUM_SOURCES=0 make dev
    ```

3. Create two new sources, each with one submission that contains both a file and a message. The message should be set to `this is the message`. The file should be called `hello.txt` and contain a single line of text: `hello`.
4. Delete the cassettes you wish to regenerate or just delete the entire directory by running:

    ```bash
    rm -r tests/functional/cassettes
    ```

5. Regenerate cassettes by running:

    ```bash
    make test-functional
    ```

Note: One of the functional tests deletes a source, so you may need to add it back in between test runs where you are generating new cassettes.

## Making a Release

1. Update versions: `./update_version.sh $new_version_number` and add a new entry in the changelog.
2. Commit the changes with commit message `securedrop-client $new_version_number` and make a PR.
3. You should confirm via a manual debian package build and manual testing in Qubes that there are no regressions (this is limited pre-release QA).
4. Once your PR is approved, you can add a tag: `git tag -a $new_version_number`.
5. Perform the release signing ceremony on the tag. Push the tag.
6. The signer should create the source tarball via `python3 setup.py sdist`.
7. Add a detached signature (with the release key) for the source tarball.
8. Submit the source tarball and signature via PR into this [repository](https://github.com/freedomofpress/securedrop-debian-packaging) along with the debian changelog addition. This tarball and changelog will be used by the package builder.


## Debugging

To use `pdb`, add these lines:

```
from PyQt5.QtCore import pyqtRemoveInputHook; pyqtRemoveInputHook()
import pdb; pdb.set_trace()
```
Then you can use [`pdb` commands](https://docs.python.org/3/library/pdb.html#debugger-commands) as normal.

Logs can be found in the `{sdc-home}/logs`. If you are debugging a version of this application installed from a deb package in Qubes, you can debug issues by looking at the log file in `~/.securedrop_client/logs/client.log`. You can also add additional log lines in the running code in
`/opt/venvs/securedrop-client/lib/python3.7/site-packages/securedrop_client/`.

Sometimes there is a bug in Qt rather than the client, so it helps to install [a debug version of PyQt5](#build-and-install-a-debug-version-of-pyqt5) which will allow you to see Qt debug symbols in your Python tracebacks. You can use `gdb` to view a traceback as well as a core file, if you're debugging a segfault, but first you must need to install the following some additional packages in order for `gdb` to work with Python programs.

```
sudo apt install libc6-dbg libpython3-all-dbg libpython3-dbg libpython3.7-dbg python3-dbg python3.7-dbg valgrind-dbg
```

### Build and install a debug version of PyQt5

1. Build a debug version of Qt 5

Clone the Qt repo and build it from source following these instructions: https://wiki.qt.io/Building_Qt_5_from_Git#Getting_the_source_code. This defaults to creating a 'debug' build and installs the binaries in the current directory, avoiding the need for `make install`. Note that the `-developer-build` option causes more symbols to be exported in order to allow more classes and functions to be unit tested than in a regular Qt build.

```
git clone https://code.qt.io/qt/qt5.git
cd qt5
git checkout v5.14.2                                # or checkout a different version
git submodule update --init --recursive
export LLVM_INSTALL_DIR=/usr/llvm
mkdir ../qt5-build && cd ../qt5-build               # we don't want to build in the source code directory
../qt5/configure -developer-build -opensource -nomake examples -nomake tests -confirm-license
make -j 4
```

2. Prepare to build PyQt5 

We are going to use the client virtual environment to build and install PyQt5. Make sure the client dependencies are installed. This will include `pyqt5-sip` which will be used when we build pyqt5 from source.

If you haven't already, download the client and set up the virtual environment. 

```
git clone git@github.com:freedomofpress/securedrop-client.git
cd securedrop-client
virtualenv --python=python3.7 .venv
source .venv/bin/activate
pip install --require-hashes -r dev-requirements.txt
```

Make sure to uninstall the prepackaged pyqt5 library since we will be using our own.

```
pip uninstall pyqt5
```

3. Download the PyQt5 source tarball from PyPi

4. Build and install PyQt5

Make sure you are still in the client virtual environment before building PyQt5.

```
tar -xzvf PyQt5-5.14.2.tar.gz
cd PyQt5-5.14.2
pip install PyQt-builder
export PATH=~/qt/qt5-build/qtbase/bin:$PATH
export QT_PLUGIN_PATH=~/qt/qt5-build/qtbase/plugins
sip-install --debug --qmake ~/qt/qt5-build/qtbase/bin/qmake --confirm-license
```

### Find/report a Qt bug

1. Create a Qt account: https://login.qt.io/register
2. Find or report a bug here: https://bugreports.qt.io
