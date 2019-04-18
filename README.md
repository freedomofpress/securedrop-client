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

## License

The Python SecureDrop SDK is licensed in the GPLv3. See [`LICENSE`](./LICENSE) for more details.
