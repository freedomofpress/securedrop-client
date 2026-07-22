> By contributing to this project, you agree to abide by our [Code of Conduct](https://github.com/freedomofpress/.github/blob/main/CODE_OF_CONDUCT.md).

# Python SDK for SecureDrop

[![CircleCI](https://circleci.com/gh/freedomofpress/securedrop-sdk/tree/main.svg?style=svg)](https://circleci.com/gh/freedomofpress/securedrop-sdk/tree/main)

This SDK provides a convenient Python interface to the [SecureDrop Journalist Interface API](https://docs.securedrop.org/en/latest/development/journalist_api.html). The development of the SDK was primarily motivated by the creation of the [SecureDrop Workstation](https://github.com/freedomofpress/securedrop-workstation) based on Qubes OS.

The SDK is currently used by the [SecureDrop Client](https://github.com/freedomofpress/securedrop-client) that is a component of the SecureDrop Workstation. When used in Qubes OS, the SDK uses the [securedrop-proxy](https://github.com/freedomofpress/securedrop-proxy) service, as the VM which runs the client does not have network access by design.

# Quick Start

```bash
make venv
source .venv/bin/activate
make test
```

We cover all the API calls supported by the SecureDrop Journalist Interface API.

To install the SDK into your `virtualenv` for testing purposes:

```
pip uninstall securedrop-sdk
pip install git+https://github.com/freedomofpress/securedrop-sdk@my_branch#egg=securedrop-sdk
```

# Upgrading one single dependency

To upgrade one single Python dependency, say `requests`, run the following:

```bash
PACKAGE=requests make upgrade-pip
```

This will upgrade both `dev-requirements` and primary `requirements`.

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

**Note:** We have a CI check that does not use the recorded API request and response data in order to make sure we are testing the latest changes to the SDK against the latest server API (see `sdk-with-server` in `.github/workflows/sdk.yml`).

We use [vcrpy](https://vcrpy.readthedocs.io/en/latest/) to record and replay API calls made over HTTP. Each request made from a test and its response from the server is stored in a "cassette" in `data` directories. Tests replay these cassettes instead of making actual API calls to a server.

## Generating new cassettes for API calls

1. Start the server in a container by running:

    ```bash
    NUM_SOURCES=5 LOADDATA_ARGS="--random-file-size 3" make dev
    ```

2. Delete the cassettes you wish to regenerate or just delete all yaml files by running:

    ```bash
    rm data/*.yml
    ```

   If you are only adding a new test and not modifying existing ones, you can
   skip this step

3. Generate new cassettes by running:

    ```bash
    make test TESTS=tests/test_api.py
    ```
Note: Some tests alter source and conversation data on the server so you may need to restart the server in between test runs.

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
