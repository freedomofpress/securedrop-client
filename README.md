# Python SDK for SecureDrop

[![CircleCI](https://circleci.com/gh/freedomofpress/securedrop-sdk/tree/master.svg?style=svg)](https://circleci.com/gh/freedomofpress/securedrop-sdk/tree/master)

This SDK provides a convenient Python interface to the [SecureDrop Journalist Interface API](https://docs.securedrop.org/en/latest/development/journalist_api.html). The development of the SDK was primarily motivated by the creation of the [SecureDrop Workstation](https://github.com/freedomofpress/securedrop-workstation) based on Qubes OS.

The SDK is currently used by the [SecureDrop Client](https://github.com/freedomofpress/securedrop-client) that is a component of the SecureDrop Workstation. When used in Qubes OS, the SDK uses the [securedrop-proxy](https://github.com/freedomofpress/securedrop-proxy) service, as the VM which runs the client does not have network access by design.

**IMPORTANT:** This project is still under active development. We do not recommend using it in any production context.

# Development

## Quick Start

```bash
pip install -U pipenv
pipenv sync --dev
pipenv shell
make test
```

This project uses `pipenv <https://docs.pipenv.org>`_ to manage all dependencies.
This is a Python 3 project. When using ``pipenv`` locally, ensure you used the ``--keep-outdated``
flag to prevent dependencies from being unnecessarily upgraded during normal development.

We cover all the API calls supported by the SecureDrop Journalist Interface API.

## Testing

The tests are located in the `tests` directory. This project uses [vcrpy]
(http://vcrpy.readthedocs.io/en/latest/) to record and then reply the API calls so that
developers will have repeatable results so that they may work offline. `vcrpy` stores YAML
recordings of the API calls in the `data` directory. 

To run all the test cases, use the following command.

```bash
make test
```

To run a single test, use this following command, replace the test case name at the end.

```bash
make test TESTS=tests/test_api.py::TestAPI::test_error_unencrypted_reply
```

To test against a live development server, you will need to run the SecureDrop
developent container from the main SecureDrop repository on your host. This
can be done via `NUM_SOURCES=5 make -C securedrop dev`.

In this repo, comment out the `@vcr` decorator of the `setUp` method in
`test_api.py` and execute which ever tests you want to run. If you want to
re-run all tests against the API, remove all the `.yml` files in the
`data` directory.

## Generating test data for `APIProxy`

To test or to generate new test data file for the `APIProxy` class in
`test_apiproxy.py` file, you will have to setup
`QubesOS <https://qubes-os.org>`_ system.

There should be one VM (let us call it `sd-journalist`), where we can run
latest securedrop server code from the development branch using
``NUM_SOURCES=5 make -C securedrop dev`` command. The same VM should also have
`securedrop-proxy` project installed, either from the source by hand or using
the latest Debian package from the FPF repository.

Below is an example configuration for proxy `/etc/sd-proxy.yaml`:

```
host: 127.0.0.1
scheme: http
port: 8081
target_vm: sd-svs
dev: False
```

Then we can create our second developent VM called `sd-svs`, in which we can checkout/develop
the `securedrop-sdk` project. The required configuration file is at `/etc/sd-sdk.conf`

```
[proxy]
name=sd-journalist
```

We should also add a corresponding entry in `/etc/qubes-rpc/policy/securedrop.Proxy` file
in **dom0**.

```
sd-svs sd-journalist allow
$anyvm $anyvm deny
```

The above mentioned setup can also be created using `securedrop-workstation` project.

Now, delete any related JSON file under `data/` directory, or remove all of
them, and then execute ``make test TEST=tests/test_apiproxy.py``. This is
command will generate the new data files, which can be used in CI or any other
system.

**Note:** Remember that file download checks don't read actual file path in the `APIProxy` tests as it requires QubesOS setup. You can manually uncomment those lines to execute them on QubesOS setup.

# Releasing

To make a release, you should:

1. Create a branch named "release-[VERSION]"
2. Update `CHANGELOG.md` and `setup.py`
3. Commit the changes.
4. Create a PR and get the PR reviewed and merged into ``master``.
5. ``git tag`` and push the new tag.
6. Checkout the new tag locally.
7. Push the new release source tarball to the PSF's PyPI `following this documentation <https://packaging.python.org/tutorials/packaging-projects/#uploading-the-distribution-archives>`_.

8. If you want to publish the new SDK release to the FPF PyPI mirror, Hop over to the the `securedrop-debian-packaging` repo and follow the [build-a-package](https://github.com/freedomofpress/securedrop-debian-packaging/blob/master/README.md#build-a-package) instructions to push the package up to our PyPI mirror: https://pypi.org/simple

# Contributing

Please read [CONTRIBUTING.md](https://github.com/freedomofpress/securedrop-sdk/CONTRIBUTING.md) for details on our code of conduct, and the process for submitting pull requests to us.

# Versioning

We use [SemVer](http://semver.org/) for versioning. For the versions available, see the [tags on this repository](https://github.com/freedomofpress/secureddrop-sdk/tags). 

# License

The Python SecureDrop SDK is licensed in the GPLv3. See [`LICENSE`](./LICENSE) for more details.
