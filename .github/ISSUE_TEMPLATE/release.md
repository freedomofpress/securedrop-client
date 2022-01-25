---
name: Release
about: Create a tracking ticket for a SecureDrop Client release

---

This issue tracks the SecureDrop Client release [version]. It will be organized by:

- Release Manager:
- Deputy Release Manager:

This release includes the following changes:
- [high level summary of changes]

SecureDrop maintainers and testers: As you QA this release, please report back your testing results as comments on this ticket. File GitHub issues for any problems found, tag them "QA: Release", and associate them with the release milestone for tracking (or ask a maintainer to do so).

## Test plan

[Once completed, insert or link to test plan here, can be left out until then]

## Release tasks

- [ ] Update changelog
- [ ] Create test plan
- [ ] Refresh nightlies
- [ ] Begin formal QA using nightlies; refresh nightlies as needed
- [ ] Build production package in standard [build environment](https://github.com/freedomofpress/securedrop-debian-packaging/wiki/FAQ#how-do-i-create-a-local-environment-suitable-for-building-packages)
- [ ] Sign production package
- [ ] Perform final pre-flight testing using apt-qa.freedom.press
  - [ ] **Localization:** In a dispVM, change your locale (e.g.: `export LANG=es_ES.utf-8; dpkg-reconfigure locales`), run the Client, and confirm that the application is translated.
- [ ] Publish production package
- [ ] Publicize release via support channels
