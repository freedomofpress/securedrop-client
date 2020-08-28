# Python SDK for SecureDrop

[![CircleCI](https://circleci.com/gh/freedomofpress/securedrop-sdk/tree/master.svg?style=svg)](https://circleci.com/gh/freedomofpress/securedrop-sdk/tree/master)

This SDK provides a convenient Python interface to the [SecureDrop Journalist Interface API](https://docs.securedrop.org/en/latest/development/journalist_api.html). The development of the SDK was primarily motivated by the creation of the [SecureDrop Workstation](https://github.com/freedomofpress/securedrop-workstation) based on Qubes OS.

The SDK is currently used by the [SecureDrop Client](https://github.com/freedomofpress/securedrop-client) that is a component of the SecureDrop Workstation. When used in Qubes OS, the SDK uses the [securedrop-proxy](https://github.com/freedomofpress/securedrop-proxy) service, as the VM which runs the client does not have network access by design.

# Development

## Quick Start

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

## Testing

The tests are located in the `tests` directory. This project uses [vcrpy](http://vcrpy.readthedocs.io/en/latest/) to record and then reply the API calls so that
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
[QubesOS](https://qubes-os.org) system.

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
@anyvm @anyvm deny
```

Now, first we have to verify that this setup works. For that, comment out the
`@dastollervey_datasaver` decorator in the setup method of `test_apiproxy.py`.
By commenting out that python decorator we make sure that our tests will do
real call to the proxy VM. You can do `journalctl -f` in `dom0` to see the log
entry that `sd-svs` is making a call to the `sd-journalist` vm, and then run
one initial test.

```
make test TESTS=tests/test_apiproxy.py::TestAPIProxy::test_api_auth
```

Remember to check the logs in `dom0`, you should see an entry like below.


```
Aug 28 15:45:13 dom0 qrexec[1474]: securedrop.Proxy: sd-svs -> sd-journalist: allowed to sd-journalist
```

If the setup is good, we should see the test passing.

## Changing a test or adding a new test in test_apiproxy.py

Say we are modifying the `test_get_sources`, now to regenerate proper test data
for the same, we should first comment out the `dastollervey_datasaver`
decorator from both `setUp` and `test_get_sources` methods. Then also remove
the `setUp.json` and `test_get_sources.json` files from `data/` directory. Now,
when we will run that one test case, it will connect to the server and fetch
real data. If you wait for 60 seconds for the next call but this time uncomment
the `dastollervey_datasaver` decorators in those two methods, it will now again
connect to the server, and also create fresh JSON data files which you can then
commit to the repository. The same steps has to be taken for any new test case
you are adding.

If your test is modifying any state in the server, then before you rerun the
test for fresh test data, you should restart the server.

**Note:** Remember that file download checks don't read actual file path in the `APIProxy` tests as it requires QubesOS setup. You can manually uncomment those lines to execute them on QubesOS setup.

# Releasing

To make a release, you should:

1. Create a branch named `release/$new_version_number`
2. Update `CHANGELOG.md` and `setup.py`
3. Commit the changes.
4. Create a PR and get the PR reviewed and merged into ``master``.
5. ``git tag $new_version_number`` and push the new tag.
6. Checkout the new tag locally.
7. Push the new release source tarball to the PSF's PyPI [following this documentation](https://packaging.python.org/tutorials/packaging-projects/#uploading-the-distribution-archives). Do not upload the wheel (by deleting it from your `dist/` directory prior to upload).
8. If you want to publish the new SDK release to the FPF PyPI mirror, Hop over to the the `securedrop-debian-packaging` repo and follow the [build-a-package](https://github.com/freedomofpress/securedrop-debian-packaging/blob/master/README.md#build-a-package) instructions to push the package up to our PyPI mirror: https://pypi.org/simple

# Contributing

Please read [CONTRIBUTING.md](https://github.com/freedomofpress/securedrop-sdk/blob/master/CONTRIBUTING.md) for details on our code of conduct, and the process for submitting pull requests to us.

# Versioning

We use [SemVer](http://semver.org/) for versioning. For the versions available, see the [tags on this repository](https://github.com/freedomofpress/securedrop-sdk/tags).

# License

The Python SecureDrop SDK is licensed in the GPLv3. See [`LICENSE`](./LICENSE) for more details.
