# Changelog

## 0.11.0

This is the first release solely targeting Debian Bookworm. New features in the securedrop-client codebases will be available on Bookworm and Qubes 4.2 only.

* Install debian package requirements via sdw-config metapackage (#1957, #1967)
* Drop Bullseye support (#1958)
* Update AppArmor __pycache__ rules for Python 3.11 (#2000, #2010)
* Implement proxy v2 in Rust (#1718, #2017, #2031, #2039, #2015)
* Provision deb822-style apt sources list (#1952)
* Use QubesDB to configure VM-specific settings (#1883, #2034)
* Use systemd and qubes services to conditionally provision VMs (#1677)
* Update release signing key expiry date (#2036)
* Clean up securedrop-log code (#2014, #2042)
* Add securedrop-qubesdb and securedrop-whonix-config packages (#2032, #2051, #2056, #2058)
* Move MIME handling to systemd services, make sd-proxy disposable (#2033)
* Add support for automatically resuming failed downloads (#2006)

* Dependencies:
  * Pillow from 10.2.0 to 10.3.0 (#1953)
  * authlib from 1.3.0 to 1.3.1 (#2063)

* Internal and development:
  * Remove the pre-commit hook for make check-strings (#1896)
  * Display package hashes after successful build (#1898)
  * Exclude client version string from Project-Id-Version of .pot files (#1915)
  * Exclude root project .venv from bandit (#1918)
  * Run tests as not-root (#1919)
  * Automatically collect package build log (#1923)
  * Use bash for all Debian packaging scripts (#1927)
  * Use ruff for formatting checks (#1885, #1944)
  * Push "nightly" after each merged PR (#1960)
  * Update readme to reference python3.11 (#1969)
  * Install xfce4-terminal in all VMs for debugging (#2013)
  * Exclude Babel header from i18n diff in make check-strings (#2054)


## 0.10.1
* Fix printing of transcripts. (#1936)

## 0.10.0

This is the first release from the merged securedrop-client repository, which now
contains the securedrop-export, securedrop-log, securedrop-proxy and securedrop-sdk
codebases. See our [blog post](https://securedrop.org/news/consolidating-securedrop-workstations-git-repositories-to-make-development-easier/) for more details.
All components now use the same version number, previous changelogs can be found in each
component's subfolder.

* VeraCrypt-encrypted USB drives are now supported for export. (#1777, #1908)
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
* Make files exported to USBs world readable (#1872, #1917)
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
  * Run CI as a non-root user. (#1919)
  * Remove __pycache__ folders from packages. (#1909)
  * Remove specific version from .pot files. (#1915)
