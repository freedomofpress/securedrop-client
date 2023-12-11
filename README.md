> [There are many ways to contribute, and we welcome your help!](CONTRIBUTING.md) By contributing to this project, you agree to abide by our [Code of Conduct](https://github.com/freedomofpress/.github/blob/main/CODE_OF_CONDUCT.md).

[![CircleCI](https://circleci.com/gh/freedomofpress/securedrop-client.svg?style=svg)](https://circleci.com/gh/freedomofpress/securedrop-client)
[![Gitter](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/freedomofpress/securedrop)

# securedrop-client

The SecureDrop Client is a desktop application for journalists to communicate with sources and work with submissions on the
[SecureDrop Workstation](https://github.com/freedomofpress/securedrop-workstation). It runs within a [Qubes OS](https://www.qubes-os.org/intro/)
virtual machine that has no direct network access and opens files within individual, non-networked, disposable VMs.

This repository contains multiple components, including:
* `client`: desktop GUI application
* `export`: logic for exporting submissions
* `log`: centralized logging
* `proxy`: restricted HTTP proxy

Each component's folder has a README with more detail.

To learn more about architecture and our rationale behind our Qubes OS approach, see the
[SecureDrop Workstation readme](https://github.com/freedomofpress/securedrop-workstation/blob/main/README.md).

**IMPORTANT:** This project is currently undergoing a pilot study and should not be used in production environments.
