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
pyenv install 3.7
pyenv local 3.7.x

brew install pip
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

### Merging Migrations

This project aims to have at most one migration per release. There may be cases where this is not feasible,
but developers should merge their migration into the latest migration that has been generated since the last
release. The above mentioned autogenerate command will not do this for you.

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

## Run the tests and checks

In order to run the test suite you should also install the `xvfb` package (to make the `xvfb-run` command available): `apt install xvfb`. You may also need to install the `sqlite3` command: `apt install sqlite3`.

To run everything, run:

```bash
make check
```

To individually run the unit tests, run `make test` to run the suite in parallel (fast), or run `make test-random` to run the tests in random order (slower, but this is what `make check` runs and what runs in CI).

### Functional Tests

Functional tests are run alone using `make test-functional` and otherwise will be ran along with `make check`.

We use `qtbot`, bundled with the [pytest-qt](https://pytest-qt.readthedocs.io/en/latest/) package, for UI interaction within our functional tests. We use [vcrpy](https://vcrpy.readthedocs.io/en/latest/) to replay the original response from the test server. These responses are stored in the `tests/functional/cassettes` directory. Our test TOTP is set to `994892` and stored in casettes.

#### Generating new cassettes

Some changes may require generating new cassettes, such as modifications to API endpoints. If you see the following warning, you may need to generate a new cassette or all new cassettes, depending on the change you made:

```
Can't overwrite existing cassette ('<path-to-cassette-for-a-functional-test>') in your current record mode ('once').
```

To generate new cassettes, follow these instructions:

1. Before generating new cassettes that will be used to replay server interaction, bypass TOTP verification so that we can use the hard-coded value of `123456` in `tests/conftest.py`. You can do this by applying the following diff to the securedrop server, which you will be running in the next step:
       ```diff
       diff --git a/securedrop/models.py b/securedrop/models.py
       index dcd26bbaf..50bc491b4 100644
       --- a/securedrop/models.py
       +++ b/securedrop/models.py
       @@ -649,6 +649,7 @@ class Journalist(db.Model):

                try:
                    user = Journalist.query.filter_by(username=username).one()
       +            return user
                except NoResultFound:
                    raise InvalidUsernameException(
                        "invalid username '{}'".format(username))
       (END)
       ```
2. Start the dev server: `NUM_SOURCES=0 make dev`
3. Set up the dev server with data required for functional tests to pass and run in any order:
    - Create 5 new sources, each with one submission that contains both a file and a message. The message should be set to `this is the message`. The file should be called `hello.txt` and contain a single line of text: `hello`.
3. Delete all the old cassettes by running `rm -r tests/functional/cassettes` or just delete the cassettes you wish to regenerate.
4. Run `make test-functional` which will regenerate cassettes for any that are missing in the `tests/functional/cassettes` folder.

Note: After generating new cassettes, the test server will be in a state with only 3 sources. If for some reason you need to try again, make sure the server has the expected 5 sources, each with one submission that contains both the expected file and message before repeating the process of deleting cassettes and regenerating them.

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
