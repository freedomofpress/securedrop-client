# Changelog

## 0.4.0

  * Reject JSON with duplicate keys (TOB-SDW-014) (#98)
  * Support Debian Bullseye (#100, #97)
  * Use reproducible wheels (#81, #85)
  * Dependency updates (#82, #88, #91, #93, #95, #96)

## 0.3.1

  * Moved proxy configuration to private volume (#79)
  * Added black and isort checks to standardise code formatting (#61)
  * Update urllib3 to version 1.25.10, requests to version 2.22.0, due to CVE-2020-26137 (#76).

## 0.3.0

  * Use incoming timeout value from JSON (#69).
  * Update PyYaml to 5.3.1 due to CVE-2020-1747 (#73).

## 0.2.1

  * Increase default timeout to 120s from 10s (#70)

## 0.2.0

  * Initial beta release.

## 0.1.7

  * Update Werkzeug to 0.16.0 due to CVE-2019-14806 (#64)

## 0.1.6

  * Fixes CI for git-lfs based package builds (#60)
  * Rename VMs (#59)
  * Restructures the code base with more object methods (#55)
  * Add quality control tools (#54)
  * Improve error handling, tests (#53)
  * Adds buster packaging in CI (#52)

## 0.1.5

  * Update build-requirements.txt to include wheels for Buster

## 0.1.4

  * Update urllib3 to version 1.24.3 or later due to CVE-2019-11324 (#35)
  * Remove pipenv in favor of pip-tools (#33)

## 0.1.3

  * Updated PyYAML to 5.1 and safe loading of YAML files
    #24 and #25

## 0.1.2

  * Update requirements: Remove dev requirements (#20), update wheel hashes
    (#21)

## 0.1.1-1

  * Resolves venv paths in generated scripts (via dh-virtualenv)

## 0.1.1

  * Update requests to 2.20.0

## 0.1.0

  * Initial release. (Closes: #XXX)
