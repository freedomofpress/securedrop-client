# Python SDK for SecureDrop

[![CircleCI](https://circleci.com/gh/freedomofpress/securedrop-sdk/tree/main.svg?style=svg)](https://circleci.com/gh/freedomofpress/securedrop-sdk/tree/main)

This SDK provides a convenient Python interface to the [SecureDrop Journalist Interface API](https://docs.securedrop.org/en/latest/development/journalist_api.html). The development of the SDK was primarily motivated by the creation of the [SecureDrop Workstation](https://github.com/freedomofpress/securedrop-workstation) based on Qubes OS.

The SDK is currently used by the [SecureDrop Client](https://github.com/freedomofpress/securedrop-client) that is a component of the SecureDrop Workstation. When used in Qubes OS, the SDK uses the [securedrop-proxy](https://github.com/freedomofpress/securedrop-proxy) service, as the VM which runs the client does not have network access by design.

# Quick Start

```bash
virtualenv --python=python3 .venv
source .venv/bin/activate
pip install --require-hashes -r dev-requirements.txt
make test
```

We cover all the API calls supported by the SecureDrop Journalist Interface API.

To install the SDK into your `virtualenv` for testing purposes:

```
pip uninstall securedrop-sdk
pip install git+https://github.com/freedomofpress/securedrop-sdk@my_branch#egg=securedrop-sdk
```

# Running tests

To run all tests and checks, run:

```bash
make check
```

To run all tests, run:

```bash
make test
```

To run all tests that make API calls over HTTP, run:

```bash
make test TESTS=tests/test_api.py
```

To run all tests that make API calls over qrexec, run:

```bash
make test TESTS=tests/test_apiproxy.py
```

To run a single test, specify file name, class name, and test name, e.g.:

```bash
make test TESTS=tests/test_api.py::TestAPI::test_get_sources
```

# Creating and updating tests

When tests are run, they replay recorded API request and response data instead of making actual API calls to a server. This is why tests can pass even when there is no server running. If the server ever changes its API or you want to add new tests that make API calls, then you'll need to record new request and response data by following the steps outlined below.

**Note:** We have a CI test that does not use the recorded API request and response data in order to make sure we are testing the latest changes to the SDK against the latest server API (see `test-against-latest-api` in https://github.com/freedomofpress/securedrop-sdk/blob/main/.circleci/config.yml).

We use [vcrpy](https://vcrpy.readthedocs.io/en/latest/) to record and replay API calls made over HTTP and a decorator called `@qrexec_datasaver` to record and replay API calls made over qrexec. Each request made from a test and its response from the server is stored in a "cassette" in the `data` directory. Tests replay these cassettes instead of making actual API calls to a server.

If you run the tests and see the following vcrpy warning, then you'll need to re-record cassettes because none of the existing cassettes contain the expected API call and we don't allow existing cassettes to be overwritten:

```
Can't overwrite existing cassette ('<path-to-cassette-for-a-functional-test>') in your current record mode ('once').
```

The steps to generate new cassettes are split into two sections based on communication protocol: [Generating cassettes for API calls over HTTP](#generating-cassettes-for-api-calls-over-http) and [Generating cassettes for API calls over qrexec](#generating-cassettes-for-api-calls-over-qrexec).

## Generating cassettes for API calls over HTTP

1. Start the server in a docker container by running:

    ```bash
    NUM_SOURCES=5 make dev
    ```

2. Delete the cassettes you wish to regenerate or just delete all yaml files by running:

    ```bash
    rm data/*.yml
    ```

   If you are only adding a new test and not modifying existing ones, you can
   skip this step, but you still need to remove the authentication setup during
   cassette generation. Otherwise you will get 403 errors for API endpoints that
   require a valid token. Remove the setup cassette by running:

   ```bash
   rm data/test-setup.yml
   ```

   (You can reinstate the unmodified version later.)

3. Generate new cassettes that make API calls over HTTP by running:

    ```bash
    make test TESTS=tests/test_api.py
    ```
Note: Some tests alter source and conversation data on the server so you may need to restart the server in between test runs.

## Generating cassettes for API calls over qrexec

In order to generate cassettes for tests that make API calls over qrexec, you'll need to run the server and proxy on a separate VM. If this is the first time you are generating cassettes, first follow the steps outlined in the [Test setup for qrexec communication](#test-setup-for-qrexec-communication) section, which will help you set up a new VM called `sd-dev-proxy`.

Once your proxy are set up, follow these steps:

1. Start the server in a docker container on `sd-dev-proxy` by running:

    ```bash
    NUM_SOURCES=5 make dev
    ```

2. [Skip if adding a new test] Delete the cassettes you wish to regenerate or just delete all json files by running:

    ```bash
    rm data/*.json
    ```

3. Comment out the `@qrexec_datasaver` decorator above the test you want to generate a new cassette for or just generate all new cassettes by commenting out the decorator above all methods in the `test_apiproxy.py::TestAPIProxy` class.

4. Make qrexec calls to the server and collect real response data:

    ```bash
    make test TESTS=tests/test_apiproxy.py
    ```

5. Uncomment the `@qrexec_datasaver` decorator wherever you commented it out.
6. Record new cassettes from the response data collected in step 4:

    ```bash
    make test TESTS=tests/test_apiproxy.py
    ```

**Note:** If you get a 403 error it's becuase the test is trying to reuse an old TOTP code, so wait for 60 seconds and try again. Some tests alter source and conversation data on the server so you should restart the server in between test runs.

## Test setup for qrexec communication

If this is the first time you are generating new cassettes that make API calls over qrexec, then you'll need to set up a new VM for running the server and proxy following these steps:

1. Create a new AppVM based on the **debian-10** template called **sd-dev-proxy**.
2. Install the lastest proxy package:

    ```bash
    wget https://apt.freedom.press/pool/main/s/securedrop-proxy/<latest-package>.deb
    dpkg -i <latest-package>.deb
    ```

3. Create `/home/user/.securedrop_proxy/sd-proxy.yaml` with the following contents (assuming the VM you'll be running the SDK tests from is called **sd-dev**):

    ```
    host: 127.0.0.1
    scheme: http
    port: 8081
    target_vm: sd-dev
    dev: False
    ```

4. Install Docker.
5. Clone `securedrop` on **sd-dev-proxy** and run the server in a Docker container:

    ```bash
    git clone https://github.com/freedomofpress/securedrop
    cd securedrop
    virtualenv .venv --python=python3
    source .venv/bin/activate
    pip install -r securedrop/requirements/python3/develop-requirements.txt
    NUM_SOURCES=5 make dev
    ```

6. Open a terminal in **sd-dev** and create `/etc/sd-sdk.conf` with the following contents:

```
[proxy]
name=sd-dev-proxy
```

7. Modify `/etc/qubes-rpc/policy/securedrop.Proxy` in **dom0** by adding the following line to the top of the file so that the sdk tests can make calls to the proxy:

```
sd-dev sd-dev-proxy allow
```

**NOTE:** You may want to switch back to the RPC configuration files in their as-provisioned state before a `make test` run in `dom0`, as this and the following change to the RPC policies will break the strict validation of the RPC policies that is one of those tests.

8. Modify `/etc/qubes-rpc/policy/qubes.Filecopy` in **dom0** by adding the following line to the top of the file so that the proxy can send files over qrexec to the sdk:

```
sd-dev-proxy sd-dev allow
```

9. Verify qrexec communication between `sd-dev-proxy` and `sd-dev` is set up properly.

    a. Run the server on `sd-dev-proxy` if it isn't already running:

    ```bash
    NUM_SOURCES=5 make dev
    ```
    b. With the main branch of this repo checked out on `sd-dev`, comment out the `@qrexec_datasaver` decorator above the `test_apiproxy.py::TestAPIProxy::setUp` method so that `test_api_auth` makes an actual API call over qrexec.
    c. Run `test_api_auth`:

    ```bash
    make test TESTS=tests/test_apiproxy.py::TestAPIProxy::test_api_auth
    ```

    **Note:** If the test fails, run `journalctl -f` in **dom0** before trying again to see if communication between `sd-dev` and `sd-dev-proxy` is being denied. A successful log looks like this:

    ```
    Aug 28 15:45:13 dom0 qrexec[1474]: securedrop.Proxy: sd-dev -> sd-dev-proxy: allowed to sd-dev-proxy
    ```

# Releasing

To make a release, you should:

1. Create a branch named `release/$new_version_number`
2. Update `CHANGELOG.md` and `setup.py`
3. Commit the changes.
4. Create a PR and get the PR reviewed and merged into ``main``.
5. ``git tag $new_version_number`` and push the new tag.
6. Checkout the new tag locally.
7. Push the new release source tarball to the PSF's PyPI [following this documentation](https://packaging.python.org/tutorials/packaging-projects/#uploading-the-distribution-archives). Do not upload the wheel (by deleting it from your `dist/` directory prior to upload).
8. If you want to publish the new SDK release to the FPF PyPI mirror, Hop over to the the `securedrop-debian-packaging` repo and follow the [build-a-package](https://github.com/freedomofpress/securedrop-debian-packaging/blob/HEAD/README.md#build-a-package) instructions to push the package up to our PyPI mirror: https://pypi.org/simple

# Contributing

Please read [CONTRIBUTING.md](https://github.com/freedomofpress/securedrop-sdk/blob/HEAD/CONTRIBUTING.md) for details on our code of conduct, and the process for submitting pull requests to us.

# Versioning

We use [SemVer](http://semver.org/) for versioning. For the versions available, see the [tags on this repository](https://github.com/freedomofpress/securedrop-sdk/tags).

# License

The Python SecureDrop SDK is licensed in the GPLv3. See [`LICENSE`](./LICENSE) for more details.
