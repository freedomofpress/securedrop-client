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
  QubesDB
* `proxy`: restricted HTTP proxy
* `workstation-config`: configuration for SecureDrop Workstation templates

Each component's folder has a README with more detail.

To learn more about architecture and our rationale behind our Qubes OS approach, see the
[SecureDrop Workstation readme](https://github.com/freedomofpress/securedrop-workstation/blob/main/README.md).


We initially piloted this project with a small number of news organizations; see [our blog post](https://securedrop.org/news/piloting-securedrop-workstation-qubes-os/)
for additional information. In July 2024, we transitioned SecureDrop Workstation to an open beta with the [1.0.0 release](https://securedrop.org/news/securedrop-workstation-1_0_0-released/).
