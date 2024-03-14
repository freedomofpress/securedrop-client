# Changelog

## 0.10.0-rc2

* Support unpartitioned VeraCrypt drives. (#1908)
* Adjust wording referring to "sd-devices" VM. (#1908)
* Remove __pycache__ folders from packages. (#1909)
* Remove specific version from .pot files. (#1915)

## 0.10.0-rc1

This is the first release from the merged securedrop-client repository, which now
contains the securedrop-export, securedrop-log, securedrop-proxy and securedrop-sdk
codebases. See our [blog post](https://securedrop.org/news/consolidating-securedrop-workstations-git-repositories-to-make-development-easier/) for more details.
All components now use the same version number, previous changelogs can be found in each component's
subfolder.

* VeraCrypt-encrypted USB drives are now supported for export. (#1777)
* Don't ask for a passphrase if the device is already unlocked ([securedrop-export#105](https://github.com/freedomofpress/securedrop-export/pull/105), #1777)
* Ensure all print jobs have been fully enqueued ([securedrop-export#105](https://github.com/freedomofpress/securedrop-export/pull/105))
* Cleanup `metadata.json` from sd-devices after exporting ([securedrop-export#105](https://github.com/freedomofpress/securedrop-export/pull/105))
* Add status code and error for multiple attached devices ([securedrop-export#105](https://github.com/freedomofpress/securedrop-export/pull/105))
* Improve detail in error messages when exporting fails and log them (#1777)
* Add spinner and active state in "Insert Encrypted Drive" dialog (#1019, #1777)
* Consistently transition to "Ready to export" state (#990, #1777)
* Fix typos in messages (#1651)
* Fix homepage URL in setup.py (#1662)
* Remove obsolete gvfs-bin dependency from securedrop-workstation-viewer (#1842)
* Set umask 0o22 before writing to USBs (#1872)
* Update translations from Weblate (#1548, #1747)
* Add `.rtf` printing support ([securedrop-export#109](https://github.com/freedomofpress/securedrop-export/pull/109))

* Dependencies:
  * Update requests to 2.31.0
  * Update certifi to 2023.7.22
  * Update jinja2 to 3.1.3

* Internal and development:
  * Fix syntax of mypy comments (#1646)
  * Pull out string "transcript.txt" into a constant (#1658)
  * Restore workaround for segmentation faults in tests (#1656)
  * Auto-detect Wayland in run.sh developer environment (#1653)
  * Verify gettext machine objects (`.mo`s) are reproducible (#1666)
  * Migrate dependency management to poetry (#1671)
  * Enable dependabot for Python and GitHub Actions (#1768, #1782, #1824, #1830)
  * Move and refactor debian/ packaging files from securedrop-builder (#1741)
  * Use `--require-hashes` when installing dependencies during package build (#1792)
  * Lint `.desktop` files in CI (#1783)
  * Apply bandit and safety linting to all components in one place (#1814)
  * Add initial configuration for Rust components (#1817, #1818)
  * Standardize `make lint` in all components (#1841)
  * Move remaining CircleCI jobs over to GitHub Actions (#1841)
  * Apply black and isort formatting to all components in one place (#1860)
  * Add shellcheck linting (#1843)
  * Stop using deprecated pkg_resources (#1851)
  * Have CI run piuparts (#1844)
  * Use dh_apparmor for installing the profile (#1856)
  * Use setuptools.find_packages() in setup.py (#1873)
  * Parameterize sender_is_current_user in test instead of randomization (#1884)
  * Stop running client tests in parallel with pytest-xdist (#1881)
  * Run lintian on Debian packages (#1845)
