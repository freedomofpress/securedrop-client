# Python SDK for SecureDrop

[![CircleCI](https://circleci.com/gh/freedomofpress/securedrop-sdk/tree/master.svg?style=svg)](https://circleci.com/gh/freedomofpress/securedrop-sdk/tree/master)

This SDK provides a convenient Python interface to the [SecureDrop Journalist Interface API](https://docs.securedrop.org/en/latest/development/journalist_api.html). The development of the SDK was primarily motivated by the creation of the [SecureDrop Workstation](https://github.com/freedomofpress/securedrop-workstation) based on Qubes OS.

The SDK is currently used by the [SecureDrop Client](https://github.com/freedomofpress/securedrop-client) that is a component of the SecureDrop Workstation. When used in Qubes OS, the SDK uses the [securedrop-proxy](https://github.com/freedomofpress/securedrop-proxy) service, as the VM which runs the client does not have network access by design.

**IMPORTANT:** This project is still under active development. We do not recommend using it in any production context.

## Developer Quick Start

```bash
pip install -U pipenv
pipenv sync --dev
pipenv shell
make test
```

More complete documentation can be found in the [`docs`](./docs) directory.

## Deployment
### Pre-release
1. Create a branch named "release-[VERSION]"
2. Update `CHANGELOG.md` and `setup.py`
3. Open a PR against the `master` branch
4. Create and push the new tag
5. Checkout the new tag before moving on to step #6
6. Build wheels and create the tarball package

   Hop over to the the `securedrop-debian-packaging` repo and follow the [build-a-package](https://github.com/freedomofpress/securedrop-debian-packaging/blob/master/README.md#build-a-package) instructions

7. Push the package up to our PyPi mirror: https://pypi.org/simple

### Release
Follow instructions in [securedrop-debian-packaging](https://github.com/freedomofpress/securedrop-debian-packaging). This is where you'll rebuild the wheels in a secure environment, verify hashes, make the debian package, update the debian package changelog to point to the changelog that you edited during the **Pre-release** step, and then push the wheels out to the test apt server. Once QA is finished, you'll push the wheels to the production apt server.

## Contributing

Please read [CONTRIBUTING.md](https://github.com/freedomofpress/secureddrop-sdk/CONTRIBUTING.md) for details on our code of conduct, and the process for submitting pull requests to us.

## Versioning

We use [SemVer](http://semver.org/) for versioning. For the versions available, see the [tags on this repository](https://github.com/freedomofpress/secureddrop-sdk/tags). 

## License

The Python SecureDrop SDK is licensed in the GPLv3. See [`LICENSE`](./LICENSE) for more details.
