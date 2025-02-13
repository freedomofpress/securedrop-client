# Changelog

## 0.14.1

This release contains fixes for two security issues; please see our advisory for more details.

* Security fixes:
  * Prevent path manipulation/traversal attacks in SDK (CVE-2025-24888)
  * Don't send source VM name to sd-log (CVE-2025-24889)

* Miscellaneous:
  * Update year in messages.pot

## 0.14.0

* Add support for selecting and deleting multiple sources (#2208, #2188, #2230, #2252, #2293, #2299, #2300)
* Use builtin `venv` module instead of `virtualenv` (#2246)
* Improve logging of API failures (#2245)
* Improve client keyboard shortcuts handling (#2209)
* Fix client crash when a source with an in-progress download is deleted (#2217)
* Improve exception handling for download failures (#2275, #2276)
* Add French language support (#2283)
* Updated multiple dependencies (#2253, #2267, #2214, #2210, #2211)

* Internal and development
  * Switch securedrop-client package Architecture to "any" (#2178)
  * Have `run.sh` automatically emit full debug logs (#2198)
  * Have `make build-debs` print tag signature, if any (#2205)
  * Upgrade Rust toolchain to 1.81.0 (#2215)
  * Fixes to SD test cassettes (#2225)
  * Re-enable `ruff` for files in proxy/ (#2234)
  * Don't have CI cancel GitHub merge queue jobs (#2235)
  * Updated multiple dependencies (#2280, #2181, #2183)

## 0.13.2

* Don't let Range header persist into other requests (#2195)
* Have BaseErrors trigger DownloadDecryptionException in download flow (#2196)

## 0.13.1

* Ensure accurate mimetype detection of Office files, add additional sample files to integration tests (#2184)
* Support direct printing of image types supported by `cups` (#2174)
* Broaden printing support to all filetypes supported by LibreOffice (#2166)
* Display an error message if user tries to print an unprintable file type (#2166)
* Use single PrintDialog GUI element for all print actions (#2143)
* Remove unused `_from_string` methods from SDK (#2144)
* Update build toolchain and `setuptools` for CVE-2024-6345 (#2136, [securedrop-builder#501](https://github.com/freedomofpress/securedrop-builder/pull/501))
* Update `ruff` to 0.5.4 (#2138)

## 0.12.0

* Support viewing .heic and .avif files (#2110)
* Fix printing of Office documents requiring conversion to PDF (#2119)
* Show error details on Error screen of Export Wizard (#2098)
* Improve Export Wizard handling of button presses (#1926)
* Add hover state and animation to Print dialog buttons (#2125)
* Upgrade `openssl` Rust crate to 0.10.66 for RUSTSEC-2024-0357 (#2131)


## 0.11.0

This is the first release solely targeting Debian Bookworm. New features in the securedrop-client codebases will be available on Bookworm and Qubes 4.2 only.

* Support Qubes 4.2 and Debian Bookworm, drop 4.1 and Bullseye support (#1958)
* Automatically resume failed downloads (#2006)
* Update AppArmor `__pycache__` rules for Python 3.11 (#2000, #2010)
* Implement proxy v2 in Rust (#1718, #2017, #2031, #2039, #2015)
* Make sd-proxy VM disposable (#2033)
* Update release signing key expiry date to May 2027 (#2036)
* Allow nautilus to have RWX memory (#2060)
* Fix print preflight status check (#2102)
* Open `.webm` videos in Totem (#2106)

* Provisioning:
  * Install debian package requirements via sdw-config metapackage (#1957, #1967)
  * Provision deb822-style apt sources list (#1952)
  * Use QubesDB to configure VM-specific settings (#1883, #2034)
  * Use systemd and Qubes services to conditionally provision VMs (#1677, #2033)
  * Configure Journalist Interface auth credentials via QubesDB (#2032, #2051, #2056, #2058)
  * Use bash for all Debian packaging scripts (#1927)

* Internal and development:
  * Remove the pre-commit hook for make check-strings (#1896)
  * Display package hashes after successful build (#1898)
  * Exclude client version string from Project-Id-Version of .pot files (#1915)
  * Exclude root project .venv from bandit (#1918)
  * Run tests as not-root (#1919)
  * Automatically collect package build log (#1923)
  * Use ruff for linting and formatting checks (#1885, #1944)
  * Push "nightly" after each merged PR (#1960)
  * Update readme to reference python3.11 (#1969)
  * Install xfce4-terminal in all VMs for debugging (#2013)
  * Exclude Babel header from i18n diff in make check-strings (#2054, #2065)
  * Reorganize securedrop-log code to clearly split server and client (#1677)
  * Clean up unused securedrop-log code (#2014, #2042)
  * Document architecture of securedrop-log component (#1995)
  * Update most development dependencies to their latest versions
  * Add QubesDB and locally built packages to piuparts (#2032, #2034)


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
