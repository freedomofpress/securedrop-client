# securedrop-client

**NOTE:**  We are currently focusing on a rewrite of this application using the Electron framework. Please see the [`app`](../app) directory for more information

The SecureDrop Client is a desktop application for journalists to communicate with sources and work with submissions on the [SecureDrop Workstation](https://github.com/freedomofpress/securedrop-workstation).

The client runs within a [Qubes OS](https://www.qubes-os.org/intro/) VM that has no direct network access and opens files within individual, non-networked, disposable VMs. API requests and responses to and from the [SecureDrop application server](https://docs.securedrop.org/en/stable/glossary.html#application-server) are sent through an intermediate VM using the [SecureDrop Proxy](https://github.com/freedomofpress/securedrop-client/tree/main/proxy).

To learn more about architecture and our rationale behind our Qubes OS approach, see the [SecureDrop Workstation readme](https://github.com/freedomofpress/securedrop-workstation/blob/main/README.md).

## Index

* [Getting Started](#getting-started)
    * [Running against a test server](#running-against-a-test-server)
    * [Developer environment](#developer-environment)
    * [Developer environment on a Linux-based non-Qubes OS](#developer-environment-on-a-linux-based-non-qubes-os)
    * [Developer environment on macOS](#developer-environment-on-macos)
        * [Set up the server](#set-up-the-server)
        * [Set up the SecureDrop Client](#set-up-the-securedrop-client)
    * [Staging environment](#staging-environment)
    * [Production environment](#production-environment)
* [Updating dependencies](#updating-dependencies)
    * [Production](#production)
    * [Development](#development)
    * [Build dependencies](#build-dependencies)
* [Generating and running database migrations](#generating-and-running-database-migrations)
* [AppArmor support](#apparmor-support)
    * [Requirements](#Requirements)
    * [Enabling AppArmor](#enabling-apparmor)
    * [Testing and updating the AppArmor profile](#testing-and-updating-the-apparmor-profile)
* [Running tests and checks](#running-tests-and-checks)
    * [Functional Tests](#functional-tests)
        * [Generating new cassettes](#generating-new-cassettes)
* [Making a Release](#making-a-release)
* [Debugging](#debugging)

## Getting Started

The quickest way to get started with running the client is to use the [developer environment](#developer-environment) that [runs against a test server running in a local docker container](#running-against-a-test-server). This differs from a staging or production environment where the client receives and sends requests over Tor. Things are a lot snappier in the developer environment and can sometimes lead to a much different user experience, which is why it is important to do end-to-end testing in Qubes using the [staging environment](#staging-environment), especially if you are modifying code paths involving how we handle server requests and responses.

For reproducing production bugs or running demos, we recommend using the [Production Environment](#production-environment) that will allow you to test a nightly build of the client.

We support running the [developer environment on a non-Qubes OS](#developer-environment-on-a-non-qubes-os) for developer convenience. If this is your preferred environment, keep in mind that you, or a PR reviewer, will need to run tests in Qubes if you modify code paths involving any of the following:

* cryptography
* opening of files in VMs
* network (via the RPC service) traffic
* fine tuning of the graphical user interface

### Comparing the development and staging/production environments

```mermaid
graph TD

subgraph "development environment"
subgraph "your development VM"
direction TB
dData(("temporary<br>directory")) --- dClient
dKeychain(("temporary<br>keychain")) --- dClient
dClient["securedrop-client<br>(./run.sh)"] --stdin/stdout/stderr--> dProxy
dProxy["securedrop-proxy<br>(built via cargo)"] --HTTP-->
dServer["SecureDrop Server<br>(make dev)"]
end
end

subgraph "staging/production environment"
spKeychain --- spClient
subgraph sd-app
spData(("~/.securedrop_client")) --- spClient
spClient["securedrop-client"]
end
spClient --stdin/stdout/stderr over qrexec--> spProxy
subgraph sd-gpg
spKeychain(("~/.gnupg"))
end
subgraph sd-proxy
spProxy["securedrop-proxy"]
end
spProxy --HTTP--> spTor
subgraph sd-whonix
spTor["Tor"]
end
spTor --> spServer["SecureDrop Server"]
end
```

### Running against a test server

In order to login, or take other actions involving network access, you will need to run the client against a SecureDrop server. If you don't have a production server or want to test against a test server, you can install a SecureDrop server inside a dev container by following the instructions [in the SecureDrop documentation](https://developers.securedrop.org/en/latest/setup_development.html#quick-start).

The client uses the [SecureDrop SDK](securedrop_client/sdk) to interact with the [SecureDrop Journalist API](https://developers.securedrop.org/en/latest/journalist_api.html). After you run the server container, the journalist interface API will be running on `127.0.0.1:8081` with a test journalist, admin, and test sources and replies.

Submissions in the SecureDrop server dev environment can be decrypted with [this test key](tests/files/securedrop.gpg.asc). The `./run.sh` script will import it for you into a temporary keyring; you may need to import it manually if you run the client by other means.

### Developer environment

**NOTE:** Tor is not used in the developer environment. If you want to use a Tor connection between the client and server, then you'll need to follow the [staging environment](#staging-environment) instructions instead.

Running the client in a developer environment will use a temporary directory as its configuration directory, instead of ` ~/.securedrop_client`. The development gpg private key inside a gpg keychain is stored in the temporary configuration directory, which will be used to decrypt messages sent from the server running in the local docker container.

The SecureDrop client will open or export file submissions within disposable AppVms.

1. Open a terminal in the `sd-app` AppVM in Qubes

2. Run a SecureDrop server in a local docker container

See the [SecureDrop docs](https://docs.securedrop.org/en/latest/development/setup_development.html) for setup instructions, including post-installation steps for allowing docker to be run as a non-root user, which is a requirement on Qubes.

3. In a new terminal tab, clone the SecureDrop Client repo and install its dependencies:

```
git clone git@github.com:freedomofpress/securedrop-client.git
cd securedrop-client/client
poetry install
```

   * You will need Python 3.11 to run the client. If it's not the default `python3` on your installation, you can set `poetry env use python3.11`.

4. Run SecureDrop Client

```
./run.sh
```

Or, if you want to persist data across restarts, you will need to run the client with:

```
./run.sh --sdc-home /path/to/my/configuration/directory
```

To log in, use one of the journalist usernames/passwords displayed in the Docker server output, such as `journalist`/`correct horse battery staple profanity oil chewy`. To generate the required 2FA token, we recommend installing and using the `oathtool` command, eg: `oathtool -b --totp "JHCOGO7VCER3EJ4L"` in your terminal. These same credentials are also displayed on https://demo.securedrop.org/ for convenience.

### Developer environment on Linux or macOS

The setup process is largely the same as above. Instead of running in `sd-app` or another Qubes VM, you'll go through the above steps in your non-Qubes environment.

Just like on Qubes, this configuration doesn't use the Tor network. In addition, the client will detect that you're not running on Qubes, and won't attempt to launch or access VMs for viewing or exporting documents.

On macOS, you can bootstrap your environment using [Homebrew](https://brew.sh). To install Python 3.11, GPG, and `oathtool` (for generating 2FA codes), use:

 `brew install python@3.11 gnupg oath-toolkit`

If you have trouble getting the SecureDrop developer environment running on macOS, but have access to a remote server, you can proxy to it using this command:

`socat TCP4-LISTEN:8081,fork,reuseaddr TCP4:A.B.C.D:8081`

### Staging environment

**NOTE:** You can use the [`try-client-pr.py`](https://github.com/freedomofpress/securedrop-workstation/blob/main/scripts/try-client-pr.py) script in the SecureDrop Workstation repository to build and install packages from a specific branch, to use with a staging or production environment.

Running the SecureDrop client in a SecureDrop Workstation staging environment will use a `~/.securedrop_client` as its configuration directory. The gpg key in the `sd-gpg` AppVM configured during `make all` will be used to decrypt messages.

The SecureDrop client will open or export file submissions within disposable AppVms.

Requests and responses between the client and server use a Tor connection, which are proxied via the `securedrop-proxy` AppVM's RPC service.

1. Run a SecureDrop staging server

See [SecureDrop docs on setting up a staging server](https://developers.securedrop.org/en/latest/virtual_environments.html#staging) or [SecureDrop docs on setting up a staging server in Qubes](https://developers.securedrop.org/en/latest/qubes_staging.html#deploying-securedrop-staging-instance-on-qubes)

2. Open a terminal in `dom0` in Qubes

3. Create a `config.json` file

```
cd securedrop-workstation
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

Or [manually initialize](https://github.com/freedomofpress/securedrop-client/blob/main/client/files/securedrop-client) the SecureDrop Client database.

7. To run a different version of the client, say the version from a branch called `<branchname>`, first add a NetVM (`sys-firewall`) to `sd-app` via its Qubes Settings so you can clone the client repository, and then follow these steps:

```
sudo apt-get install git pipx  # NB. won't persist across "sd-app" reboots
pipx ensurepath
pipx install poetry # Install poetry version => 2.x.x, < 3.x
git clone -b <branchname> https://github.com/freedomofpress/securedrop-client.git
cd securedrop-client
poetry install
```

8. Run the client

```
poetry run python -m securedrop_client
```

### Production environment

**NOTE:** You can use the [`try-client-pr.py`](https://github.com/freedomofpress/securedrop-workstation/blob/main/scripts/try-client-pr.py) script in the SecureDrop Workstation repository to build and install packages from a specific branch, to use with a staging or production environment.

Running the SecureDrop client in a SecureDrop Workstation production environment will use a `~/.securedrop_client` as its configuration directory. The gpg key in the `sd-gpg` AppVM configured during `make all` will be used to decrypt messages.

The SecureDrop client will open or export file submissions within disposable AppVms.

Requests and responses between the client and server use a Tor connection, which are proxied via the `securedrop-proxy` AppVM's RPC service.

1. Run a SecureDrop server

See [SecureDrop docs on setting up a server](https://docs.securedrop.org/en/stable/admin/installation/installation_overview.html) if you want to use a production server for a fully production-like environment.

2. Open a terminal in `dom0` in Qubes

3. Create a `config.json` file

```
cd securedrop-workstation
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

## Updating dependencies

`pyproject.toml` and `Poetry.lock` point to hashes of artifacts hosted on PyPI, and `build-requirements.txt` points to our reproducible builds of the wheels (https://github.com/freedomofpress/securedrop-builder/). Whenever a dependency in `build-requirements.txt` changes, our team needs to manually review the code in the dependency diff with a focus on spotting vulnerabilities.

If you're adding or updating a production dependency, you need to:

1. Modify `pyproject.toml`.
2. Build the relevant wheels in the `securedrop-builder` Git repository.
3. Synchronize `build-requirements.txt` with hashes of the newly built wheels.

## Generating and running database migrations

```bash
rm -f svs.sqlite
sqlite3 svs.sqlite .databases > /dev/null
alembic upgrade head
alembic revision --autogenerate -m "describe your revision here"
```

**NOTE.**  Schema migrations, data migrations, and tests [MUST] be self-contained.  That is, their `upgrade()` and `downgrade()` methods and their tests [MUST NOT] rely, directly or indirectly, on other project code, such as `db.py`'s SQLAlchemy models or other helper classes and functions defined outside of the migration under test, because these utilities may change in Git over time.  (The scaffolding of the `test_alembic.py` test suite [MAY] rely on such utilities, because it is versioned at the Git level, not the Alembic level.)  See [#1500](https://github.com/freedomofpress/securedrop-client/issues/1500) for an example of why this guideline applies.

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

There are two packages you'll have to install manually in order to run the entire test suite:

`apt install xvfb`
`apt install sqlite3`

We launch tests via `xvfb-run` on an `xvfb` X server in order to support machines with no display hardware, like we have in CircleCI. Even when running tests on a machine with display hardware, `xvfb` is useful in that it prevents a bunch of windows and dialogs from popping up on your desktop. If you want to run tests without `xvfb` then you can just uninstall it and run thet tests and checks as described below.

NOTE: `xvfb-run` will start and stop `xvfb` for you.

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

We use [vcrpy](https://vcrpy.readthedocs.io/en/latest/) to record and replay API calls. Each request made from a test and response from the server is stored in a "cassette" yaml file in the `tests/functional/data` directory.

If the server changes its API, then you'll see the following warning indicating that a request failed to be found in an existing cassette and that you'll need to regenerate cassettes:

```
Can't overwrite existing cassette ('<path-to-cassette-for-a-functional-test>') in your current record mode ('once').
```

To set up a local dev server and generate cassettes, follow these steps:

1. Disable one TOTP check so that we can re-use the same one-time-code. You can do this by applying the following patch to the server code:

    ```
    diff --git a/securedrop/models.py b/securedrop/models.py
    index e70e492fc..bdbc55a06 100644
    --- a/securedrop/models.py
    +++ b/securedrop/models.py
    @@ -645,7 +645,7 @@ class Journalist(db.Model):

            # Reject OTP tokens that have already been used
            if self.last_token is not None and self.last_token == sanitized_token:
    -            raise two_factor.OtpTokenInvalid("Token already used")
    +            pass

            if self.is_totp:
                # TOTP
    ```

2. Start the server in a docker container and add 5 sources with messages, files, and replies by running:

    ```bash
    NUM_SOURCES=5 make dev
    ```

3. Delete the cassettes you wish to regenerate or just delete the entire directory by running:

    ```bash
    rm -r tests/functional/data
    ```

4. Regenerate cassettes by running:

    ```bash
    make test-functional
    ```

Note: One of the functional tests deletes a source, so you may need to add it back or restart the server in between test runs where you are generating new cassettes.

## Making a Release

See our [documentation for releasing SecureDrop Workstation Debian packages](https://developers.securedrop.org/en/latest/workstation_release_management.html#release-a-debian-package).

## Debugging

To use `pdb`, add these lines:

```
from PyQt5.QtCore import pyqtRemoveInputHook; pyqtRemoveInputHook()
import pdb; pdb.set_trace()
```
Then you can use [`pdb` commands](https://docs.python.org/3/library/pdb.html#debugger-commands) as normal.

Logs can be found in the `{sdc-home}/logs`. If you are debugging a version of this application installed from a deb package in Qubes, you can debug issues by looking at the log file in `~/.securedrop_client/logs/client.log`. You can also add additional log lines in the running code in
`/opt/venvs/securedrop-client/lib/python3.11/site-packages/securedrop_client/`.


[MAY]: https://datatracker.ietf.org/doc/html/rfc2119#section-5
[MUST]: https://datatracker.ietf.org/doc/html/rfc2119#section-1
[MUST NOT]: https://datatracker.ietf.org/doc/html/rfc2119#section-2
